module Expr where

open import Data.Empty
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.Fin.Properties renaming (_≟_ to _≟Fin_)
open import Data.Product using (∃; _,_)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

FName : Set
FName = String

FNames : Set
FNames = List FName

data Expr : ℕ → Set where
   num : ∀ {n} → ℕ → Expr n
   bv  : ∀ {n} → (i : Fin n) → Expr n
   fv  : ∀ {n} → (x : FName) → Expr n
   ƛ   : ∀ {n} → (e : Expr (suc n)) → Expr n
   _·_ : ∀ {n} → (f : Expr n) → (e : Expr n) → Expr n

Expr0 : Set
Expr0 = Expr zero

num-cong : ∀ {i x y} → num {i} x ≡ num y → x ≡ y
num-cong refl = refl

bv-cong : ∀ {i x y} → bv {i} x ≡ bv y → x ≡ y
bv-cong refl = refl

_≟E_ : ∀ {n} → Decidable {A = Expr n} _≡_
num x ≟E num y   with x ≟ℕ y
num x ≟E num .x | yes refl = yes refl
num x ≟E num y  | no ¬p = no (λ q → ¬p (num-cong q))
-- italy?
--   where postulate italy? : _
num x ≟E bv i    = no (λ ())
num x ≟E fv y    = no (λ ())
num x ≟E ƛ u     = no (λ ())
num x ≟E (u · b) = no (λ ())
--
bv i ≟E num x   = no (λ ())
bv i ≟E bv j    with i ≟Fin j
bv i ≟E bv .i | yes refl = yes refl
bv i ≟E bv j  | no ¬p = no (λ q → ¬p (bv-cong q))
bv i ≟E fv x    = no (λ ())
bv i ≟E ƛ u     = no (λ ())
bv i ≟E (u · b) = no (λ ())
--
fv x ≟E num y   = no (λ ())
fv x ≟E bv i    = no (λ ())
fv x ≟E fv y    with x ≟S y
fv x ≟E fv .x | yes refl = yes refl
fv x ≟E fv y  | no ¬p = no italy?
   where postulate italy? : _
fv x ≟E ƛ u     = no (λ ())
fv x ≟E (u · b) = no (λ ())
--
ƛ t ≟E num x   = no (λ ())
ƛ t ≟E bv i    = no (λ ())
ƛ t ≟E fv x    = no (λ ())
ƛ t ≟E ƛ u     with t ≟E u
ƛ t ≟E ƛ .t | yes refl = yes refl
ƛ t ≟E ƛ u  | no ¬p = no italy?
   where postulate italy? : _
ƛ t ≟E (u · b) = no (λ ())
--
(t · a) ≟E num x   = no (λ ())
(t · a) ≟E bv i    = no (λ ())
(t · a) ≟E fv x    = no (λ ())
(t · a) ≟E ƛ u     = no (λ ())
(t · a) ≟E (u · b) with t ≟E u | a ≟E b
(t · a) ≟E (.t · .a) | yes refl | yes refl = yes refl
(t · a) ≟E (.t · b) | yes refl | no ¬q = no italy?
   where postulate italy? : _
(t · a) ≟E (u · .a) | no ¬p | yes refl = no italy?
   where postulate italy? : _
(t · a) ≟E (u · b) | no ¬p | no ¬q     = no italy?
   where postulate italy? : _

{- ################## -}
{- free variable name -}
{- ################## -}

fvars : ∀ {n} → Expr n → FNames
fvars (num x) = []
fvars (bv i)  = []
fvars (fv x)  = x ∷ []
fvars (ƛ f)   = fvars f
fvars (f · x) = fvars f ++ fvars x

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
↑expr (num i) = num i
↑expr (bv i)   = bv (inject₁ i)
↑expr (fv x)   = fv x
↑expr (ƛ e)    = ƛ (↑expr e)
↑expr (e · e₁) = ↑expr e · ↑expr e₁
