module Ctx where
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open import Data.List.All as All
open Any.Membership-≡
-- using (_∈_; _∉_; _⊆_; _⊈_)
-- .
open import Data.Empty using (⊥-elim)
-- open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
-- . x
open import Types
open import Expr
open import FVar
-- .
Assoc : Set → Set → Set
Assoc A B = List (A × B)
-- .
Ctx : Set
Ctx = Assoc FName LType
-- .
CtxI : Set
CtxI = Assoc FName IType
-- .
dom : ∀ {A B} → Assoc A B → List A
dom = Data.List.map proj₁
-- .
data DualDomDist {A B : Set} : Assoc A B → Assoc A B → Set where
    [] : DualDomDist [] []
    _∷ᵣ_ : ∀ {Γ Δ x τ}
        → (x∉ : x ∉ dom (Γ ++ Δ))
        → DualDomDist Γ Δ
        → DualDomDist Γ ((x , τ) ∷ Δ)
    _∷ₗ_ : ∀ {Γ Δ x τ}
        → (x∉ : x ∉ dom (Γ ++ Δ))
        → DualDomDist Γ Δ
        → DualDomDist ((x , τ) ∷ Γ) Δ
-- .
data DomDist {A : Set} : Assoc FName A → Set where
    [] : DomDist []
    _∷_ : ∀ {Γ x τ}
         → (x∉ : x ∉ dom Γ)
         → DomDist Γ
         → DomDist ((x , τ) ∷ Γ)
-- .

postulate
    ∈-++-weaken : ∀ {A : Set} {x : A} xs ys zs
                  → x ∈ (xs ++ zs) → x ∈ (xs ++ ys ++ zs)
    DDD-insert : ∀ {A B} (Γ Δ1 Δ2 : Assoc A B) x {τ}
               → DualDomDist Γ (Δ1 ++ Δ2)
               → x ∉ dom (Γ ++ Δ1 ++ Δ2)
               → DualDomDist Γ (Δ1 ++ [ x , τ ] ++ Δ2)

∈-tail : ∀ {A : Set} {y x : A} {xs} → ¬ (y ≡ x) → y ∈ (x ∷ xs) → y ∈ xs
∈-tail {A} {y} {x} {xs} ¬y≡x (here y≡x) = ⊥-elim (¬y≡x y≡x)
∈-tail {A} {y} {x} {xs} ¬y≡x (there y∈xs) = y∈xs

∉-¬≡ : ∀ {A : Set} {x y : A} {L : List A} → y ∉ (x ∷ L) → ¬ (y ≡ x)
∉-¬≡ y∉x∷L refl = y∉x∷L (here refl)

¬≡-sym : ∀ {A : Set} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
¬≡-sym ¬x≡y refl = ¬x≡y refl
    -- ≠-sym x≠y refl = x≠y refl
    -- ddd-r-assoc : ∀ {Γ Δ1 Δ2 a} → DualDomDist Γ (a ∷ (Δ1 ++ Δ2)) → DualDomDist Γ (Δ1 ++ [ a ] ++ Δ2)
    -- ddd-l-assoc : ∀ {Γ1 Γ2 Δ a} → DualDomDist (a ∷ (Γ1 ++ Γ2)) Δ → DualDomDist (Γ1 ++ [ a ] ++ Γ2) Δ
-- .
