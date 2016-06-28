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
    -- locally nameless
    fv  : ∀ {n} → (x : FName) → Expr n
    bv  : ∀ {n} → (i : Fin n) → Expr n
    -- ⊸-I/E
    ƛ   : ∀ {n} → (body : Expr (suc n)) → Expr n
    _·_ : ∀ {n} → (f : Expr n) → (e : Expr n) → Expr n
    -- ⟪⟫-I/E
    !_  : ∀ {n} → Expr n → Expr n
    ask_be!then_ : ∀ {n}
        → (e : Expr n)
        → (f : Expr n)
        → Expr n
    -- &-I/E
    ⟨_∣_⟩ : ∀ {n} → (f : Expr n) → (g : Expr n) → Expr n
    fst   : ∀ {n} → (e : Expr n) → Expr n
    snd   : ∀ {n} → (e : Expr n) → Expr n
    -- ⊗-I/E
    ⟨_×_⟩ : ∀ {n} → (e₁ : Expr n) → (e₂ : Expr n) → Expr n
    -- ask_be⟨_×_⟩then_ : ∀ {n}
    ask_be⟨×⟩then_ : ∀ {n}
        → (e  : Expr n)
        → (f : Expr n)
        → Expr n
    -- ⊕-I/E
    inl : ∀ {n} → (e : Expr n) → Expr n
    inr : ∀ {n} → (e : Expr n) → Expr n
    match_of_or_ : ∀ {n}
        → (e  : Expr n)
        → (f : Expr n)
        → (g : Expr n)
        → Expr n

Expr0 : Set
Expr0 = Expr zero

f0 : ∀ {n} → Fin (suc n)
f0 = zero
f1 : ∀ {n} → Fin (suc (suc n))
f1 = suc f0
f2 : ∀ {n} → Fin (suc (suc (suc n)))
f2 = suc f1
f3 : ∀ {n} → Fin (suc (suc (suc (suc n))))
f3 = suc f2
f4 : ∀ {n} → Fin (suc (suc (suc (suc (suc n)))))
f4 = suc f3

ex : Expr 2
ex = bv f0  ·      --   f0 ─⟶ the 1st nearest ƛ out here
   ( bv f1  ·      --   f1 ─⟶ the 2nd nearest ƛ out here
     (ƛ ( bv f0 ·  -- ƛ f0 ─⟶ this ƛ
        ⟨ bv f1 ∣  -- ƛ f1 ─⟶ the 1st nearest ƛ out here
          bv f2 ⟩  -- ƛ f2 ─⟶ the 2nd nearest ƛ out here
        )))

-- 747 - 723 = 2.4

{- ################## -}
{- free variable name -}
{- ################## -}

fvars : ∀ {n} → Expr n → FNames
fvars (num x) = []
fvars (fv x) = [ x ]
fvars (bv i) = []
fvars (ƛ x) = fvars x
fvars (f · g) = fvars f ++ fvars g
-- .
fvars (! e) = fvars e
fvars (ask e be!then f) = fvars f
-- .
fvars ⟨ f ∣ g ⟩ = fvars f ++ fvars g
fvars (fst x) = fvars x
fvars (snd x) = fvars x
-- .
fvars ⟨ f × g ⟩ = fvars f ++ fvars g
fvars (ask e be⟨×⟩then f) = fvars f
-- .
fvars (inl x) = fvars x
fvars (inr x) = fvars x
fvars (match e of f or g) = fvars f ++ fvars g

{- ########################################### -}
{- generate a fresh new name for free variable -}
{- ########################################### -}

postulate fresh-gen      : FNames → FName
postulate fresh-gen-spec : ∀ ns → fresh-gen ns ∉ ns

genName : (ns : FNames) → ∃ (λ x → x ∉ ns)
genName ns = fresh-gen ns , fresh-gen-spec ns

-- .

↓ℕ≠ℕ : ∀ {n m} {i : Fin m} → ¬ (suc n ≡ toℕ (suc i)) → ¬ (n ≡ toℕ i)
↓ℕ≠ℕ {n} {m} {i} sn≠si n≡i rewrite n≡i = sn≠si refl
-- .
↓fin : ∀ {n : ℕ} → (i : Fin (suc n)) → ¬ (n ≡ toℕ i) → Fin n
↓fin {zero} zero     0≠0 with 0≠0 refl
↓fin {zero} zero     0≠0 | ()
↓fin {zero} (suc ()) 0≠n
↓fin {suc n} zero    i≠0   = zero
↓fin {suc n} (suc i) sn≠si = suc (↓fin {n} i (↓ℕ≠ℕ sn≠si))
-- .
↑fin : ∀ {n} → Fin n → Fin (suc n)
↑fin = inject₁

-- Increasing all fin within the given exp by 1 on type level
-- without actually changing exp.
↑bv : ∀ {n} → Expr n → Expr (suc n)
↑bv (num x) = num x
↑bv (fv x) = fv x
↑bv (bv i) = bv (↑fin i)    -- ☆ ☆ ☆ type only
↑bv (ƛ e) = ƛ (↑bv e)
↑bv (f · e) = ↑bv f · ↑bv e
↑bv (! x) = ! ↑bv x
↑bv (ask x be!then f) =
    ask ↑bv x be!then ↑bv f
↑bv ⟨ x ∣ x₁ ⟩ = ⟨ ↑bv x ∣ ↑bv x₁ ⟩
↑bv (fst x) = fst (↑bv x)
↑bv (snd x) = snd (↑bv x)
↑bv ⟨ x × x₁ ⟩ = ⟨ ↑bv x × ↑bv x₁ ⟩
↑bv (ask x be⟨×⟩then f) =
    ask ↑bv x be⟨×⟩then ↑bv f
↑bv (inl x) = inl (↑bv x)
↑bv (inr x) = inr (↑bv x)
↑bv (match x of f or g) =
    match ↑bv x of ↑bv f or ↑bv g
-- .
↑expr : ∀ {n} → Expr n → Expr (suc n)
↑expr (num x) = num x
↑expr (fv x) = fv x
↑expr (bv i) = bv (suc i)  -- ☆ ☆ ☆ type and term
↑expr (ƛ e) = ƛ (↑expr e)
↑expr (f · e) = ↑expr f · ↑expr e
↑expr (! x) = ! ↑expr x
↑expr (ask x be!then f) =
    ask ↑expr x be!then ↑expr f
↑expr ⟨ x ∣ x₁ ⟩ = ⟨ ↑expr x ∣ ↑expr x₁ ⟩
↑expr (fst x) = fst (↑expr x)
↑expr (snd x) = snd (↑expr x)
↑expr ⟨ x × x₁ ⟩ = ⟨ ↑expr x × ↑expr x₁ ⟩
↑expr (ask x be⟨×⟩then f) =
    ask ↑expr x be⟨×⟩then ↑expr f
↑expr (inl x) = inl (↑expr x)
↑expr (inr x) = inr (↑expr x)
↑expr (match x of f or g) =
    match ↑expr x of ↑expr f or ↑expr g
