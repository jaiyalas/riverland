module Typing where
-- .
-- open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; _,_)
-- open import Data.Product hiding (map)
-- open import Data.Bool using (not)
-- open import Data.String using (_==_)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)
-- .
open import Expr
open import Types
open import Substitution
-- open Substitution.Lazy
-- .
data _,_⊢_∶_ : Ctx → Ctx → Expr 0 → LType → Set where
    litℕ : ∀ {n Γ [Γ]} → Γ , [Γ]  ⊢ num n ∶ Num
    -- -----------------------
    -- ## id/variable rules ##
    -- -----------------------
    var : ∀ {x A Γ [Γ]}
        → DomDist Γ
        → (x , A) ∈ Γ
        → Γ , [Γ] ⊢ fv x ∶ A
    var! : ∀ {x A Γ [Γ]}
        → DomDist [Γ]
        → (x , A) ∈ [Γ]
        → Γ , [Γ] ⊢ fv x ∶ A
    -- --------------
    -- ## ⟪⟫ rules ##
    -- --------------
    ⟪⟫-I : ∀ {Γ [Γ] t A}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ ! t ∶ ⟪ A ⟫
    ⟪⟫-E : ∀ L {Γ [Γ] Δ [Δ] x t u A B}
        → Γ , [Γ] ⊢ t ∶ ⟪ A ⟫
        → (x ∉ L → Δ , (x , A) ∷ [Δ] ⊢ u ∶ B)
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ ask t be!then (bv-closing u x) ∶ B
        -- 把 u 裡面的 fv x 變成 bv 0
    -- -------------
    -- ## ⊸ rules ##
    -- -------------
    ⊸-I : ∀ L {Γ [Γ] x t A B}
        → (x ∉ L → ((x , A) ∷ Γ) , [Γ] ⊢ t ∶ B)
        → Γ , [Γ] ⊢ ƛ (bv-closing t x) ∶ (A ⊸ B)
        -- 把 u 裡面的 fv x 變成 bv n, (here n = 0)
    ⊸-E : ∀ {Γ [Γ] Δ [Δ] A B t u}
        → Γ , [Γ] ⊢ t ∶ (A ⊸ B)
        → Δ , [Δ] ⊢ u ∶ A
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ t · u ∶ B
    -- -------------
    -- ## & rules ##
    --  (privilege)
    -- -------------
    &-I : ∀ {Γ [Γ] t u A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ u ∶ B
        → Γ , [Γ] ⊢ ⟨ t ∣ u ⟩ ∶ (A & B)
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
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ ⟨ t × u ⟩ ∶ (A ⊗ B)
    ⊗-E : ∀ L {Γ [Γ] Δ [Δ] t u A B C x y}
        → Γ , [Γ] ⊢ t ∶ (A ⊗ B)
        → (x ∉ L → y ∉ L → ((x , A) ∷ ((y , B) ∷ Δ)) , [Δ] ⊢ u ∶ C)
        → (Γ ++ Δ) , ([Γ] ++ [Δ])
            ⊢ ask t be⟨×⟩then bv-closing (bv-closing u y) x ∶ C
    -- -------------
    -- ## ⊕ rules ##
    -- -------------
    ⊕-I₁ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ inl t ∶ (A ⊕ B)
    ⊕-I₂ : ∀ {Γ [Γ] u A B}
        → Γ , [Γ] ⊢ u ∶ B
        → Γ , [Γ] ⊢ inr u ∶ (A ⊕ B)
    ⊕-E : ∀ L {Γ [Γ] Δ [Δ] t f g x y A B C}
        → Γ , [Γ] ⊢ t ∶ (A ⊕ B)
        → (x ∉ L → ((x , A) ∷ Δ) , [Δ] ⊢ f ∶ C)
        → (y ∉ L → ((y , B) ∷ Δ) , [Δ] ⊢ g ∶ C)
        → (Γ ++ Δ) , ([Γ] ++ [Δ])
            ⊢ match t of bv-closing f x or bv-closing g y ∶ C

-- .
