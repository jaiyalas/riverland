module Ctx where
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open import Data.List.All as All
open Any.Membership-≡ using (_∈_; _∉_; _⊆_; _⊈_)
-- .
open import Data.Empty using (⊥-elim)
-- open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
-- .
open import Types
open import Expr
open import FVar
-- .
Assoc : Set → Set → Set
Assoc A B = List (A × B)
-- .
dom : ∀ {A B} → Assoc A B → List A
dom = Data.List.map proj₁
-- .
data DualDomDist {A B : Set} : Assoc A B → Assoc A B → Set where
    [] : DualDomDist [] []
    _∷ᵣ_ : ∀ {Γ Δ x τ}
        → x ∉ dom (Γ ++ Δ)
        → DualDomDist Γ Δ
        → DualDomDist Γ ((x , τ) ∷ Δ)
    _∷ₗ_ : ∀ {Γ Δ x τ}
        → x ∉ dom (Γ ++ Δ)
        → DualDomDist Γ Δ
        → DualDomDist ((x , τ) ∷ Γ) Δ
-- .
data DomDist {A : Set} : Assoc FName A → Set where
    [] : DomDist []
    _∷_ : ∀ {Γ x τ}
         → (x∉ : x ∉ (Data.List.map proj₁ Γ))
         → DomDist Γ
         → DomDist ((x , τ) ∷ Γ)
-- .
Ctx : Set
Ctx = Assoc FName LType
-- .
CtxI : Set
CtxI = Assoc FName IType
-- .
