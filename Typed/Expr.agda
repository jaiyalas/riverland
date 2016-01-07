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

-- ############################################ --

data Typ : Set where
   numᵗ : Typ
   _⊃_ : Typ → Typ → Typ
   _∧_ : Typ → Typ → Typ
   _∨_ : Typ → Typ → Typ

-- 改天應該用 Fin 重做 FName

FName : Set
FName = String

FNames : Set
FNames = List FName

Assoc : Set → Set → Set
Assoc A B = List (A × B)

-- Ctx : ℕ → Set
-- Ctx i = Assoc (Fin i) Typ
Ctx : Set
Ctx = Assoc FName Typ


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
   match_of_∔_ : ∀ {n}
          → (t : Expr n)
          → (e₁ : Expr n)
          → (e₂ : Expr n)
          → Expr n

Expr0 : Set
Expr0 = Expr zero

{- ################## -}
{- free variable name -}
{- ################## -}

fvars : ∀ {n} → Expr n → FNames
fvars x = {!   !}
-- fvars (num x) = []
-- fvars (bv i)  = []
-- fvars (fv x)  = x ∷ []
-- fvars (ƛ τ f)   = fvars f
-- fvars (f · x) = fvars f ++ fvars x

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

-- ↑expr : ∀ {n} → Expr n → Expr (suc n)
-- ↑expr = {!   !}
-- ↑expr (num i) = num i
-- ↑expr (bv i)   = bv (inject₁ i)
-- ↑expr (fv x)   = fv x
-- ↑expr (ƛ τ e)    = ƛ τ (↑expr e)
-- ↑expr (e · e₁) = ↑expr e · ↑expr e₁
