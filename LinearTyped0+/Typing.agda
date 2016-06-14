module Typing where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; _,_)
open import Data.Product hiding (map)
open import Data.Bool using (not)
open import Data.String using (_==_)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

open import Expr
open import Types
open import Substitution

-- .
-- data DomDist : Ctx → Set where
data DomDist {A : Set} : Assoc FName A → Set where
    [] : DomDist []
    _∷_ : ∀ {Γ x τ}
         → (x∉ : x ∉ (Data.List.map proj₁ Γ))
         → DomDist Γ
         → DomDist ((x , τ) ∷ Γ)
-- .

rmEle : FName → Ctx → Ctx
rmEle x = filter (λ a → not ((proj₁ a) == x))

{-
require something from [Γ]:
    + contraction
    + ⟪⟫-I (i.e. !-I )
    + ⟪⟫-E (i.e. !-E)
require something from Γ (i.e. <Γ>):
    + ⊸-I
    + ⊗-E
    + ⊕-E
-}

data _,_⊢_∶_ {n : ℕ} : Ctx → Ctx → Expr n → LType → Set where
    -- ----------------------
    -- ## structural rules ##
    -- ----------------------
    weakening : ∀ L {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ B
        → ∀ x → x ∉ L → Γ , (x , A) ∷ [Γ] ⊢ t ∶ B
    -- weakening : ∀ L {Γ [Γ] x t A B}
    --     → Γ , [Γ] ⊢ t ∶ B
    --     → x ∉ L → Γ , (x , A) ∷ [Γ] ⊢ t ∶ B
    contraction : ∀ L {Γ [Γ] y z t A B}
        -- what's the scope of L?
        → (y ∉ L → z ∉ L → Γ , ((y , A) ∷ ((z , A) ∷ [Γ])) ⊢ t ∶ B)
        → ∀ x → x ∉ L → Γ , ((x , A) ∷ [Γ]) ⊢ [ y ↝ fv x ] ([ z ↝ fv x ] t) ∶ B
    exchange : ∀ {Γ [Γ] Δ [Δ] t A}
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ t ∶ A
        → (Δ ++ Γ) , ([Δ] ++ [Γ]) ⊢ t ∶ A
    -- -----------------------
    -- ## id/variable rules ##
    -- -----------------------
    var : ∀ {Γ [Γ] x A}
        --   → DomDist Γ -- why this one?
        → (x , A) ∈ Γ
        → Γ , [Γ] ⊢ fv x ∶ A
    var! : ∀ {Γ [Γ] x A}
        → (x , A) ∈ [Γ]
        → Γ , [Γ] ⊢ fv x ∶ A
    -- --------------
    -- ## ⟪⟫ rules ##
    -- --------------
    ⟪⟫-I : ∀ {[Γ] t A}
        → [] , [Γ] ⊢ t ∶ A
        → [] , [Γ] ⊢ ! t ∶ ⟪ A ⟫
    -- ⟪⟫-I : ∀ {Γ [Γ] t A}
    --     → [] , [Γ] ⊢ t ∶ A
    --     → Γ , [Γ] ⊢ t ∶ A
    --     → Γ , [Γ] ⊢ ! t ∶ ⟪ A ⟫
    ⟪⟫-E : ∀ {Γ [Γ] Δ [Δ] x t u A B}
        → Γ , [Γ] ⊢ t ∶ ⟪ A ⟫
        → ((x , A) ∈ [Δ] → Δ , [Δ] ⊢ u ∶ B)
        → (Γ ++ Δ) , ([Γ] ++ rmEle x [Δ])
            ⊢ ask t be! ! (fv x) then u ∶ B
    -- -------------
    -- ## ⊸ rules ##
    -- -------------
    ⊸-I : ∀ {Γ [Γ] x t A B}
        → (L : FNames)
        → ((x , A) ∈ Γ → Γ , [Γ] ⊢ t ∶ B)
        → (rmEle x Γ) , [Γ] ⊢ ƛ t ∶ (A ⊸ B)
    ⊸-E : ∀ {Γ [Γ] Δ [Δ] A B t u}
        → Γ , [Γ] ⊢ t ∶ (A ⊸ B)
        → Δ , [Δ] ⊢ u ∶ A
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ t · u ∶ B
    -- -------------
    -- ## & rules ##
    -- -------------
    &-I : ∀ {Γ [Γ] t u A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ u ∶ B
        → Γ , [Γ] ⊢ ⟨ t × u ⟩ ∶ (A & B)
    &-E₁ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ (A & B)
        → Γ , [Γ] ⊢ fst t ∶ A
    &-E₂ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ (A & B)
        → Γ , [Γ] ⊢ snd t ∶ B
    -- -------------
    -- ## ⊗ rules ##
    -- -------------
    ⊗-I : ∀ {Γ [Γ] Δ [Δ] t u A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Δ , [Δ] ⊢ u ∶ B
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ ⟨ t ∣ u ⟩ ∶ (A ⊗ B)
    ⊗-E : ∀ {Γ [Γ] Δ [Δ] t u A B C x y}
        → (L : FNames) → x ∉ L → y ∉ L
        → Γ , [Γ] ⊢ t ∶ (A ⊗ B)
        -- → ((x , A) ∷ ((y , B) ∷ Δ)) , [Δ] ⊢ u ∶ C
        → ((x , A) ∈ Γ → (y , B) ∈ Γ → (Δ , [Δ] ⊢ u ∶ C))
        → (Γ ++ (rmEle x (rmEle y Δ))) , ([Γ] ++ [Δ])
            ⊢ ask t be⟨ fv x ∣ fv y ⟩then u ∶ C
    -- -------------
    -- ## ⊕ rules ##
    -- -------------
    ⊕-I₁ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ inl t ∶ (A ⊕ B)
    ⊕-I₂ : ∀ {Γ [Γ] u A B}
        → Γ , [Γ] ⊢ u ∶ B
        → Γ , [Γ] ⊢ inr u ∶ (A ⊕ B)
    ⊕-E : ∀ {Γ [Γ] Δ [Δ] t f g x y A B C}
        → (L : FNames)
        → Γ , [Γ] ⊢ t ∶ (A ⊕ B)
        → (x ∉ L → (x , A) ∈ Δ → Δ , [Δ] ⊢ f ∶ C)
        → (y ∉ L → (y , B) ∈ Δ → Δ , [Δ] ⊢ g ∶ C)
        → (Γ ++ (rmEle x (rmEle y Δ))) , ([Γ] ++ [Δ])
            ⊢ match t of fv x ⇒ f or fv y ⇒ g ∶ C

-- .
