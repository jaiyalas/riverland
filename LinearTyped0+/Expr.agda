module Expr where
-- .
open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.Fin.Properties renaming (_≟_ to _≟Fin_)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)
-- .
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
-- .
open import Types

-- Fin n  is a type with n elements
-- Expr n is a type with n "unbounded" bounded-variables
--      using ƛ to reduce n by 1 on the type level

-- One have two intuitional interpretations of `Expr n`.
-- 1. `Expr n` is a type with n "unbounded" bounded variables.
-- 2. `Expr (suc n)` is an exp that has (bv n) as its biggest bounded variable.

data Expr : ℕ → Set where
    -- for variable naming
    num : ∀ {n} → ℕ → Expr n
    fv  : ∀ {n} → (x : FName) → Expr n
    bv  : ∀ {n} → (i : Fin n) → Expr n
    -- ⊸-I/E
    ƛ   : ∀ {n} → (body : Expr (suc n)) → Expr n
    _·_ : ∀ {n} → (f : Expr n) → (e : Expr n) → Expr n
    -- ⟪⟫-I/E
    !_  : ∀ {n} → Expr n → Expr n
    ask_be!_then_ : ∀ {n}
        → (e₁ : Expr n)
        → (fv₁ : Expr n)
        → (f : Expr n)
        → Expr n
    -- &-I/E
    ⟨_×_⟩ : ∀ {n} → (e₁ : Expr n) → (e₂ : Expr n) → Expr n
    fst   : ∀ {n} → (e : Expr n) → Expr n
    snd   : ∀ {n} → (e : Expr n) → Expr n
    -- ⊗-I/E
    ⟨_∣_⟩ : ∀ {n} → (e₁ : Expr n) → (e₂ : Expr n) → Expr n
    ask_be⟨_∣_⟩then_ : ∀ {n}
          → (e  : Expr n)
          → (fv₁ : Expr n)
          → (fv₂ : Expr n)
          → (f : Expr n)
          → Expr n
    -- ⊕-I/E
    inl : ∀ {n} → (e : Expr n) → Expr n
    inr : ∀ {n} → (e : Expr n) → Expr n
    match_of_⇒_or_⇒_ : ∀ {n}
          → (e  : Expr n)
          → (fv₁  : Expr n)
          → (f₁ : Expr n)
          → (fv₂  : Expr n)
          → (f₂ : Expr n)
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
fvars (ƛ x) = fvars x
fvars (x · x₁) = fvars x ++ fvars x₁
-- .
fvars (! e) = fvars e
fvars (ask e be! e₁ then f) = fvars f
-- .
fvars ⟨ x × x₁ ⟩ = fvars x ++ fvars x₁
fvars (fst x) = fvars x
fvars (snd x) = fvars x
-- .
fvars ⟨ x ∣ x₁ ⟩ = fvars x ++ fvars x₁
fvars (ask e be⟨ e₁ ∣ e₂ ⟩then e₃) = fvars e₃
-- .
fvars (inl x) = fvars x
fvars (inr x) = fvars x
fvars (match e of x₁ ⇒ f₁ or x₂ ⇒ f₂) = fvars f₁ ++ fvars f₂

{- ########################################### -}
{- generate a fresh new name for free variable -}
{- ########################################### -}

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

-- reduce fin by 1 on type level but not data level
↓fin : ∀ {n} → (i : Fin (suc n)) → ¬ (n ≡ toℕ i) → Fin n
↓fin {zero} zero 0≠0 with 0≠0 refl
↓fin {zero} zero 0≠0 | ()
↓fin {zero} (suc ()) 0≠n
↓fin {suc n} zero i≠0 = zero
↓fin {suc n} (suc i) sn≠si = suc (↓fin i (↓ℕ≠ℕ sn≠si))

-- Increasing all fin within the given exp by 1 on type level
-- without actually changing exp.
↑expr : ∀ {n} → Expr n → Expr (suc n)
↑expr (num x) = num x
↑expr (fv x) = fv x
↑expr (bv i) = bv (inject₁ i) -- inject₁ ≡ ↑fin
↑expr (ƛ e) = ƛ (↑expr e)
↑expr (f · e) = ↑expr f · ↑expr e
↑expr (! x) = ! ↑expr x
↑expr (ask x be! x₁ then x₂) =
    ask ↑expr x be! ↑expr x₁ then ↑expr x₂
↑expr ⟨ x × x₁ ⟩ = ⟨ ↑expr x × ↑expr x₁ ⟩
↑expr (fst x) = fst (↑expr x)
↑expr (snd x) = snd (↑expr x)
↑expr ⟨ x ∣ x₁ ⟩ = ⟨ ↑expr x ∣ ↑expr x₁ ⟩
↑expr (ask x be⟨ x₁ ∣ x₂ ⟩then x₃) =
    ask ↑expr x be⟨ ↑expr x₁ ∣ ↑expr x₂ ⟩then ↑expr x₃
↑expr (inl x) = inl (↑expr x)
↑expr (inr x) = inr (↑expr x)
↑expr (match x of x₁ ⇒ x₂ or x₃ ⇒ x₄) = match ↑expr x of ↑expr x₁ ⇒ ↑expr x₂ or ↑expr x₃ ⇒ ↑expr x₄

postulate ↓expr' : ∀ {n} → Expr (suc n) → Expr n

-- ↓expr : ∀ {n} → Expr (suc n) → Expr n
-- ↓expr (num x) = num x
-- ↓expr (fv x) = fv x
-- -- .
-- ↓expr (bv i) = {!   !}
-- -- ↓expr {n} (bv i) with n ≟ℕ toℕ i
-- -- ↓expr {n} (bv i) | yes p = {!   !}
-- -- ↓expr {n} (bv i) | no ¬p = bv (↓fin i ¬p)
-- -- .
-- ↓expr (ƛ t) = ƛ (↓expr t)
-- ↓expr (t · t₁) = ↓expr t · ↓expr t₁
-- ↓expr (! t) = ! ↓expr t
-- ↓expr (ask t be! t₁ then t₂) = ask ↓expr t be! ↓expr t₁ then ↓expr t₂
-- ↓expr ⟨ t × t₁ ⟩ = ⟨ ↓expr t × ↓expr t₁ ⟩
-- ↓expr (fst t) = fst (↓expr t)
-- ↓expr (snd t) = snd (↓expr t)
-- ↓expr ⟨ t ∣ t₁ ⟩ = ⟨ ↓expr t ∣ ↓expr t₁ ⟩
-- ↓expr (ask t be⟨ t₁ ∣ t₂ ⟩then t₃) = ask ↓expr t be⟨ ↓expr t₁ ∣ ↓expr t₂ ⟩then ↓expr t₃
-- ↓expr (inl t) = inl (↓expr t)
-- ↓expr (inr t) = inr (↓expr t)
-- ↓expr (match t of t₁ ⇒ t₂ or t₃ ⇒ t₄) = match ↓expr t of ↓expr t₁ ⇒ ↓expr t₂ or ↓expr t₃ ⇒ ↓expr t₄
-- -- .



-- .
