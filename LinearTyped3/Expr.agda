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
-- .
FName : Set
FName = String
-- .
FNames : Set
FNames = List FName
-- .
data Expr : ℕ → Set where
    num : ∀ {n} → ℕ → Expr n
    -- .
    fv  : ∀ {n} → (x : FName) → Expr n
    bv  : ∀ {n} → (i : Fin n) → Expr n
    -- ⊸-I/E
    ƛ   : ∀ {n} → (f : Expr (suc n)) → Expr n
    _·_ : ∀ {n} → (f : Expr n) → (e : Expr n) → Expr n
    -- ⟪⟫-I/E
    bang_  : ∀ {n} → Expr n → Expr n
    ask_be!then_ : ∀ {n}
        → (e : Expr n)
        → (f : Expr (suc n))
        → Expr n
    -- ⊗-I/E
    ⟨_×_⟩ : ∀ {n} → (e₁ : Expr n) → (e₂ : Expr n) → Expr n
    ask_be⟨×⟩then_ : ∀ {n}
        → (e : Expr n)
        → (f : Expr (suc (suc n)))
        → Expr n
    -- ⊕-I/E
    inl : ∀ {n} → (e : Expr n) → Expr n
    inr : ∀ {n} → (e : Expr n) → Expr n
    match_of_or_ : ∀ {n}
        → (e  : Expr n)
        → (f : Expr (suc n))
        → (g : Expr (suc n))
        → Expr n
    -- &-I/E
    ⟨_∣_⟩ : ∀ {n} → (f : Expr n) → (g : Expr n) → Expr n
    fst   : ∀ {n} → (e : Expr n) → Expr n
    snd   : ∀ {n} → (e : Expr n) → Expr n
-- .

-- .
↓fin : ∀ {n : ℕ} → (i : Fin (suc n)) → ¬ (n ≡ toℕ i) → Fin n
↓fin {zero} zero     0≠0 with 0≠0 refl
↓fin {zero} zero     0≠0 | ()
↓fin {zero} (suc ()) 0≠n
↓fin {suc n} zero    i≠0   = zero
↓fin {suc n} (suc i) sn≠si = suc (↓fin {n} i (↓ℕ≠ℕ sn≠si))
    where
        ↓ℕ≠ℕ : ∀ {n m} {i : Fin m} → ¬ (suc n ≡ toℕ (suc i)) → ¬ (n ≡ toℕ i)
        ↓ℕ≠ℕ {n} {m} {i} sn≠si n≡i rewrite n≡i = sn≠si refl
-- .
↑fin : ∀ {n} → Fin n → Fin (suc n)
↑fin = inject₁
-- .
↑bv : ∀ {n} → Expr n → Expr (suc n)
↑bv (num x) = num x
↑bv (fv x) = fv x
↑bv (bv i) = bv (↑fin i)    -- ☆ ☆ ☆ type only
↑bv (ƛ e) = ƛ (↑bv e)
↑bv (f · e) = ↑bv f · ↑bv e
↑bv (bang x) = bang ↑bv x
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
↑expr (bang x) = bang ↑expr x
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

-- .
