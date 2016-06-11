module LJ where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; _,_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

open import Expr
open import Substitution

Ctx : Set
Ctx = Assoc FName Typ

data DomDist : Ctx → Set where
  [] : DomDist []
  _∷_ : ∀ {Γ x τ}
        → (x∉ : x ∉ (Data.List.map proj₁ Γ))
        → DomDist Γ
        → DomDist ((x , τ) ∷ Γ)

postulate _++C_ : Ctx → Ctx → Ctx

-- ############################################ --

data _⊢_∶_ : Ctx → Expr 0 → Typ → Set where
   {- ##### Axiom ##### -}
   var : ∀ {Γ x τ}
         → DomDist Γ
         → (x , τ) ∈ Γ → Γ ⊢ fv x ∶ τ
   num : ∀ {Γ} i → Γ ⊢ num i ∶ numᵗ
   {- ##### ∧-I/E ##### -}
   ∧-L₁ : ∀ {Γ A B C t a}
        → (L : FNames)
        → ( a ∉ L → ((  a ,      A)  ∷ Γ) ⊢ t ∶ C)
        → (∀ a×b → a×b ∉ L → ((a×b , (A ∧ B)) ∷ Γ) ⊢ [ a ↝ fst (fv a×b) ] t ∶ C)
   ∧-L₂ : ∀ {Γ A B C t b}
        → (L : FNames)
        → ( b ∉ L → (( b ,      B)  ∷ Γ) ⊢ t ∶ C)
        → (∀ a×b → a×b ∉ L →
            ((a×b , (A ∧ B)) ∷ Γ) ⊢
               [ b ↝ snd (fv a×b) ] t ∶ C)
   ∧-R : ∀ {Γ Δ a A b B}
       → Γ ⊢ a ∶ A
       → Δ ⊢ b ∶ B
       → (Γ ++C Δ) ⊢ ⟨ a , b ⟩ ∶ (A ∧ B)
   {- ##### ∨-I/E ##### -}
   ∨-L : ∀ {Γ A B C u v x y}
       → (L : FNames)
       → (x ∉ L → ((x , A) ∷ Γ) ⊢ u ∶ C)
       → (y ∉ L → ((y , B) ∷ Γ) ⊢ v ∶ C)
       → (∀ z → z ∉ L →
          ((z , (A ∨ B)) ∷ Γ) ⊢
            match (fv z)
               of u or v ∶ C)
   ∨-R₁ : ∀ {Γ A B a}
        → Γ ⊢ a ∶ A
        → Γ ⊢ inl a ∶ (A ∨ B)
   ∨-R₂ : ∀ {Γ A B b}
        → Γ ⊢ b ∶ A
        → Γ ⊢ inr b ∶ (A ∨ B)
   {- ##### ⊃-I/E ##### -}
   ⊃-L : ∀ {Γ Δ A B C x t u}
       → (L : FNames)
       → Γ ⊢ t ∶ A
       → (x ∉ L → ((x , B) ∷ Δ) ⊢ u ∶ C)
       → (∀ f → f ∉ L →
            (Δ ++C ((f , A ⊃ B) ∷ Γ)) ⊢ [ x ↝ ( fv f · t ) ] u ∶ C)
   ⊃-R : ∀ {Γ A B f}
       → (L : FNames)
       → (∀ x → x ∉ L → ((x , A) ∷ Γ) ⊢ (f ₀↦ (fv x)) ∶ B)
       → Γ ⊢ (ƛ A f) ∶ (A ⊃ B)
   -- ⊃-R : ∀ {Γ A B x f}
   --     → (L : FNames)
   --     → (x ∉ L → ((x , A) ∷ Γ) ⊢ f ∶ B)
   --     → Γ ⊢ ƛ A (f ₀↤ x) ∶ (A ⊃ B)






-- .
