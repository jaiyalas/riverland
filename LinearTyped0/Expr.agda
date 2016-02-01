module Expr where

open import Data.Empty
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.Fin.Properties renaming (_≟_ to _≟Fin_)
open import Data.Product using (∃; _,_)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

data Typ : Set where
   numᵗ : Typ
   _⊃_ : Typ → Typ → Typ
   _∧_ : Typ → Typ → Typ
   _∨_ : Typ → Typ → Typ

-- 改天應該用 Fin 重做 FName

Assoc : Set → Set → Set
Assoc A B = List (A × B)

FName : Set
FName = String

FNames : Set
FNames = List FName

-- ############################################ --
data Expr : ℕ → Set where
   num : ∀ {n} → ℕ → Expr n
   fv  : ∀ {n} → (x : FName) → Expr n
   bv  : ∀ {n} → (i : Fin n) → Expr n
   -- ⊃-I/E
   ƛ   : ∀ {n} → Typ → (e : Expr (suc n)) → Expr n
   _·_ : ∀ {n} → (f : Expr n) → (e : Expr n) → Expr n
   -- ∧-I/E
   ⟨_,_⟩ : ∀ {n} → (e₁ : Expr n) → (e₂ : Expr n) → Expr n
   fst : ∀ {n} → (e : Expr n) → Expr n
   snd : ∀ {n} → (e : Expr n) → Expr n
   -- ∨-I/E
   inl : ∀ {n} → (e : Expr n) → Expr n
   inr : ∀ {n} → (e : Expr n) → Expr n
   match_of_⟩_or_⟩_ : ∀ {n}
          → (t  : Expr n)
          → (u  : Expr n)
          → (e₁ : Expr n)
          → (v  : Expr n)
          → (e₂ : Expr n)
          → Expr n

Expr0 : Set
Expr0 = Expr zero

{- ################## -}
{- free variable name -}
{- ################## -}

fvars : ∀ {n} → Expr n → FNames
fvars (num x) = []
fvars (fv x) = [ x ]
fvars (bv i) = []
fvars (ƛ τ x) = fvars x
fvars (x · x₁) = fvars x ++ fvars x₁
fvars ⟨ x , x₁ ⟩ = fvars x ++ fvars x₁
fvars (fst x) = fvars x
fvars (snd x) = fvars x
fvars (inl x) = fvars x
fvars (inr x) = fvars x
-- %%%%%%%%%%% Question %%%%%%%%%%% --
fvars (match x of t ⟩ x₁ or u ⟩ x₂ ) = 先混過去
   where postulate 先混過去 : _

postulate fresh-gen      : FNames → FName
postulate fresh-gen-spec : ∀ ns → fresh-gen ns ∉ ns

genName : (ns : FNames) → ∃ (λ x → x ∉ ns)
genName ns = fresh-gen ns , fresh-gen-spec ns

{- ################## -}
{- related properties -}
{- ################## -}

↓ℕ≠ℕ : ∀ {n m} {i : Fin m}
     → ¬ (suc n ≡ toℕ (suc i))
     → ¬ (n ≡ toℕ i)
↓ℕ≠ℕ {n} {m} {i} sn≠si n≡i rewrite n≡i = sn≠si refl

↓fin : ∀ {n} → (i : Fin (suc n)) → ¬ (n ≡ toℕ i) → Fin n
↓fin {zero} zero 0≠0 with 0≠0 refl
↓fin {zero} zero 0≠0 | ()
↓fin {zero} (suc ()) 0≠n
↓fin {suc n} zero i≠0 = zero
↓fin {suc n} (suc i) sn≠si = suc (↓fin i (↓ℕ≠ℕ sn≠si))

↑expr : ∀ {n} → Expr n → Expr (suc n)
↑expr (num x) = num x
↑expr (fv x) = fv x
↑expr (bv i) = bv (inject₁ i)
↑expr (ƛ τ e) = ƛ τ (↑expr e)
↑expr (f · e) = ↑expr f · ↑expr e
↑expr ⟨ e₁ , e₂ ⟩ = ⟨ ↑expr e₁ , ↑expr e₂ ⟩
↑expr (fst e) = fst (↑expr e)
↑expr (snd e) = snd (↑expr e)
↑expr (inl e) = inl (↑expr e)
↑expr (inr e) = inr (↑expr e)
↑expr (match x of t ⟩ x₁ or u ⟩ x₂ ) = 先混過去
   where postulate 先混過去 : _
   -- match ↑expr t of ↑expr e₁ ∔ ↑expr e₂





-- .
