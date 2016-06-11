module Typing where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; _,_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

open import Expr
open import Types
open import Substitution

-- ############################################ --

-- Ctx : ℕ → Set
-- Ctx i = Assoc (Fin i) Typ
Ctx : Set
Ctx = Assoc FName LType

Ctx! : Set
Ctx! = Assoc FName IType

data DomDist {A : Set} : Assoc FName A → Set where
-- data DomDist : Ctx → Set where
    [] : DomDist []
    _∷_ : ∀ {Γ x τ}
         → (x∉ : x ∉ (Data.List.map proj₁ Γ))
         → DomDist Γ
         → DomDist ((x , τ) ∷ Γ)

-- ############################################ --

data _,_⊢_∶_ {n : ℕ} : Ctx → Ctx → Expr n → LType → Set where
    num : ∀ {Γ [Γ]} i → Γ , [Γ] ⊢ num i ∶ numᵗ
    -- {- ##### Exchange rules ##### -}
        -- done by Assoc and ∈
    -- {- ##### Contraction rules ##### -}
    weaken : ∀ {Γ [Γ] t x A B}
        → (L : FNames) → x ∉ L
        → Γ , [Γ] ⊢ t ∶ B
        → Γ , (x , A) ∷ [Γ] ⊢ t ∶ B
    -- {- ##### Weakening rules ##### -}
    contract : ∀ {Γ [Γ] t A B y z}
        → (L : FNames) → y ∉ L → z ∉ L
        → Γ , (y , A) ∷ ((z , A) ∷ [Γ]) ⊢ t ∶ B
        → (∀ x → x ∉ L → Γ , (x , A) ∷ [Γ] ⊢ [ y ↝ fv x ] ([ z ↝ fv x ] t) ∶ B)
    -- {- ##### id-I/E ##### -}
    var! : ∀ {Γ [Γ] x τ} → DomDist [Γ]
          → (x , τ) ∈ [Γ]
          → Γ , [Γ] ⊢ fv x ∶ ⟪ τ ⟫
    var : ∀ {Γ [Γ] x τ} → DomDist Γ
        → (x , τ) ∈ Γ
        → Γ , [Γ] ⊢ fv x ∶ τ
    -- {- ##### ⟪_⟫-I/E ##### -}
    ⟪⟫-I : ∀ {Γ [Γ] t A}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ ! t ∶ ⟪ A ⟫
    ⟪⟫-E : ∀ {Γ [Γ] Δ [Δ] t u A B x}
        → (L : FNames) → x ∈ L
        → Γ , [Γ] ⊢ t ∶ ⟪ A ⟫
        → Δ , ((x , A) ∷ [Δ]) ⊢ u ∶ B
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ ask t be ! (fv x) then u ∶ B
    -- {- ##### ⊸-I/E ##### -}
    ⊸-I : ∀ {Γ [Γ] t A B}
        → (L : FNames)
        → (∀ x → x ∉ L → ((x , A) ∷ Γ) , [Γ] ⊢ t ∶ B)
        → Γ , [Γ] ⊢ ƛ A t ∶ (A ⊸ B)
    ⊸-E : ∀ {Γ [Γ] Δ [Δ] A B t u}
        → Γ , [Γ] ⊢ t ∶ (A ⊸ B)
        → Δ , [Δ] ⊢ u ∶ A
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ t · u ∶ B
    -- {- ##### &-I/E ##### -}
    &-I : ∀ {Γ [Γ] Δ [Δ] t u A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Δ , [Δ] ⊢ u ∶ B
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ ⟨ t × u ⟩ ∶ (A & B)
    &-E₁ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ (A & B)
        → Γ , [Γ] ⊢ fst t ∶ A
    &-E₂ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ (A & B)
        → Γ , [Γ] ⊢ snd t ∶ B
    -- {- ##### ⊗-I/E ##### -}
    ⊗-I : ∀ {Γ [Γ] Δ [Δ] t u A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Δ , [Δ] ⊢ u ∶ B
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ ⟨ t ∣ u ⟩ ∶ (A ⊗ B)
    ⊗-E : ∀ {Γ [Γ] Δ [Δ] t u A B C x y}
        → (L : FNames) → x ∉ L → y ∉ L
        → Γ , [Γ] ⊢ t ∶ (A ⊗ B)
        → ((x , A) ∷ ((y , B) ∷ Δ)) , [Δ] ⊢ u ∶ C
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ both t of ⟨ fv x ∣ fv y ⟩ then u ∶ C
    -- {- ##### ⊕-I/E ##### -}
    ⊕-I₁ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ inl t ∶ (A ⊕ B)
    ⊕-I₂ : ∀ {Γ [Γ] u A B}
        → Γ , [Γ] ⊢ u ∶ B
        → Γ , [Γ] ⊢ inr u ∶ (A ⊕ B)
    ⊕-E : ∀ {Γ [Γ] Δ [Δ] t u v A B C}
        → (L : FNames)
        → Γ , [Γ] ⊢ t ∶ (A ⊕ B)
        → (∀ x → x ∉ L → ((x , A) ∷ Δ) , [Δ] ⊢ u ∶ C)
        → (∀ y → y ∉ L → ((y , B) ∷ Δ) , [Δ] ⊢ v ∶ C)
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ match t of u or v ∶ C
