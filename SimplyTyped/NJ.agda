module NJ where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; _,_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

open import Expr
open import Substitution

-- ############################################ --

-- Ctx : ℕ → Set
-- Ctx i = Assoc (Fin i) Typ
Ctx : Set
Ctx = Assoc FName Typ

-- data DomDist {A B : Set} : Assoc A B → Set where
data DomDist : Ctx → Set where
  [] : DomDist []
  _∷_ : ∀ {Γ x τ}
        → (x∉ : x ∉ (Data.List.map proj₁ Γ))
        → DomDist Γ
        → DomDist ((x , τ) ∷ Γ)

-- data _⊢_∶_ {n : ℕ} : Ctx → Expr n → Typ → Set where
data _⊢_∶_ : Ctx → Expr 0 → Typ → Set where
   {- ##### Axiom ##### -}
   var : ∀ {Γ x τ}
         → DomDist Γ
         → (x , τ) ∈ Γ → Γ ⊢ fv x ∶ τ
   num : ∀ {Γ} i → Γ ⊢ num i ∶ numᵗ
   {- ##### ∧-I/E ##### -}
   ∧-I : ∀ {Γ t u A B}
         → Γ ⊢ t ∶ A
         → Γ ⊢ u ∶ B
         → Γ ⊢ ⟨ t , u ⟩ ∶ (A ∧ B)
   ∧-E₁ : ∀ {Γ t A B}
          → Γ ⊢ t ∶ (A ∧ B)
          → Γ ⊢ fst t ∶ A
   ∧-E₂ : ∀ {Γ u A B}
          → Γ ⊢ u ∶ (A ∧ B)
          → Γ ⊢ snd u ∶ B
   {- ##### ∨-I/E ##### -}
   ∨-I₁ : ∀ {Γ t A B}
        → Γ ⊢ t ∶ A
        → Γ ⊢ inl t ∶ (A ∨ B)
   ∨-I₂ : ∀ {Γ u A B}
        → Γ ⊢ u ∶ B
        → Γ ⊢ inr u ∶ (A ∨ B)
   ∨-E : ∀ {Γ A B C t u v}
       → (L : FNames)
       → Γ ⊢ t ∶ (A ∨ B)
       → (∀ x → x ∉ L → ((x , A) ∷ Γ) ⊢ u ∶ C)
       → (∀ y → y ∉ L → ((y , B) ∷ Γ) ⊢ v ∶ C)
       → Γ ⊢ match t of u or v ∶ C
   {- ##### ⊃-I/E ##### -}
   ⊃-I : ∀ {Γ A B f}
         → (L : FNames)
         → (∀ a → a ∉ L
                → ((a , A) ∷ Γ) ⊢ (f ₀↦ (fv a)) ∶ B)
         → Γ ⊢ (ƛ A f) ∶ (A ⊃ B)
   ⊃-E : ∀ {Γ f a A B}
         → Γ ⊢ f ∶ (A ⊃ B)
         → Γ ⊢ a ∶ A
         → Γ ⊢ (f · a) ∶ B
