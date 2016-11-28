module Reduction where
-- .
open import Data.Nat
open import Data.Sum
open import Relation.Nullary using (¬_)
-- .
open import Expr
-- .

-- normal form? I guess
data HNF {n : ℕ} : Expr n → Set where
    numHNF : ∀ i → HNF (num i)
    ƛHNF   : ∀ f → HNF (ƛ f)
-- .

hnf? : ∀ {n} →(e : Expr n) → (HNF e ⊎ ¬(HNF e))
hnf? (num x) = {!   !}
hnf? (fv x) = {!   !}
hnf? (bv i) = {!   !}
hnf? (ƛ e) = {!   !}
hnf? (e · e₁) = {!   !}
hnf? (bang e) = {!   !}
hnf? (ask e be!then e₁) = {!   !}
hnf? ⟨ e × e₁ ⟩ = {!   !}
hnf? (ask e be⟨×⟩then e₁) = {!   !}
hnf? (inl e) = {!   !}
hnf? (inr e) = {!   !}
hnf? (match e of e₁ or e₂) = {!   !}
hnf? ⟨ e ∣ e₁ ⟩ = {!   !}
hnf? (fst e) = {!   !}
hnf? (snd e) = {!   !}

data _⟼_ {n : ℕ} : Expr n → Expr n → Set where
    -- num
    -- fv
    -- bv
    -- ·
    -- ƛ
    -- bang
    -- ask_be!then_
    -- ⟨_×_⟩
    -- ask_be⟨×⟩then_
    -- inl
    -- inr
    -- match_of_or_
    -- ⟨_∣_⟩
    -- fst
    -- snd
