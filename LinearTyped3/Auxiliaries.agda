module Auxiliaries where
-- .s
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
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
-- .
open import Ctx
-- .
data _⊹_≡_ {A : Set} : List A → List A → List A → Set where
    [] : [] ⊹ [] ≡ []
    cons-l : ∀ {xs ys zs} x → xs ⊹ ys ≡ zs → (x ∷ xs) ⊹ ys ≡ (x ∷ zs)
    cons-r : ∀ {xs ys zs} y → xs ⊹ ys ≡ zs → xs ⊹ (y ∷ ys) ≡ (y ∷ zs)
-- .
⊹≡-insertMiddle-l : ∀ {A Δ1 Δ2 Δₗ Δᵣ} (x : A) → Set
⊹≡-insertMiddle-l {_} {Δ1} {Δ2} {Δₗ} {Δᵣ} x =
    ∃ (λ Δ11 →
        ∃ (λ Δ12 →
            Δ11 ++ Δ12 ≡ Δ1 × ((Δ11 ++ [ x ] ++ Δ12) ⊹ Δ2 ≡ (Δₗ ++ [ x ] ++ Δᵣ))
            ))
⊹≡-insertMiddle-r : ∀ {A Δ1 Δ2 Δₗ Δᵣ} (x : A) → Set
⊹≡-insertMiddle-r {_} {Δ1} {Δ2} {Δₗ} {Δᵣ} x =
    ∃ (λ Δ21 →
        ∃ (λ Δ22 →
            Δ21 ++ Δ22 ≡ Δ2 × (Δ1 ⊹ (Δ21 ++ [ x ] ++ Δ22) ≡ (Δₗ ++ [ x ] ++ Δᵣ))
            ))
postulate
    ⊹≡-insertMiddle : ∀ {A Δ1 Δ2 Δₗ Δᵣ} (x : A)
        → (h : Δ1 ⊹ Δ2 ≡ (Δₗ ++ Δᵣ))
        → ⊹≡-insertMiddle-l {_} {Δ1} {Δ2} {Δₗ} {Δᵣ} x -- h
        ⊎ ⊹≡-insertMiddle-r {_} {Δ1} {Δ2} {Δₗ} {Δᵣ} x -- h
-- 沒用到
map-dom-⊹≡ : ∀ {A B Γ Γ1 Γ2}
    → (_⊹_≡_ {(A × B)} Γ1 Γ2 Γ)
    → (dom Γ1) ⊹ (dom Γ2) ≡ (dom Γ)
map-dom-⊹≡ [] = []
map-dom-⊹≡ (cons-l (proj₁ , proj₂) ls) = cons-l proj₁ (map-dom-⊹≡ ls)
map-dom-⊹≡ (cons-r (proj₁ , proj₂) ls) = cons-r proj₁ (map-dom-⊹≡ ls)

-- ddd-r-assoc : ∀ {Γ Δ1 Δ2 a} → DualDomDist Γ (a ∷ (Δ1 ++ Δ2)) → DualDomDist Γ (Δ1 ++ [ a ] ++ Δ2)
-- ddd-l-assoc : ∀ {Γ1 Γ2 Δ a} → DualDomDist (a ∷ (Γ1 ++ Γ2)) Δ → DualDomDist (Γ1 ++ [ a ] ++ Γ2) Δ

-- .
postulate
    ≡-comm' : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    ∈-++-weaken : ∀ {A : Set} {x : A} xs ys zs
                  → x ∈ (xs ++ zs) → x ∈ (xs ++ ys ++ zs)
    DDD-insert : ∀ {A B} (Γ Δ1 Δ2 : Assoc A B) x {τ}
               → DualDomDist Γ (Δ1 ++ Δ2)
               → x ∉ dom (Γ ++ Δ1 ++ Δ2)
               → DualDomDist Γ (Δ1 ++ [ (x , τ) ] ++ Δ2)
    ∉-++-tail : ∀ {A : Set} {x : A} xs ys zs
                → x ∉ (xs ++ ys ++ zs)
                → x ∉ (ys ++ zs)
    ∉-++-dropMiddle : ∀ {A : Set} {x : A} xs ys zs
                → x ∉ (xs ++ ys ++ zs)
                → x ∉ (xs ++ zs)
    pleaseKillMe : ∀ {A B : Set} {Γ2 xs ys : Assoc A B} (x : A)
                → x ∉ (dom Γ2) ++ (dom (xs ++ ys))
                → x ∉ dom (Γ2 ++ xs ++ ys)
    justKillMe : ∀ {A B : Set} {Γ Γ1 Γ2 Δₗ Δᵣ Δ1 Δ2 xs ys : Assoc A B} (x : A)
            → Γ1 ⊹ Γ2 ≡ Γ
            → Δ1 ⊹ Δ2 ≡ (Δₗ ++ Δᵣ)
            → xs ++ ys ≡ Δ2
            → x ∉ dom (Γ ++ Δₗ ++ Δᵣ)
            → x ∉ dom Γ1 ++ dom Γ2 ++ dom (xs ++ ys) -- Δ2
    justKillMe' : ∀ {A B : Set} {Γ Γ1 Γ2 Δₗ Δᵣ Δ1 Δ2 xs ys : Assoc A B} (x : A)
            → Γ1 ⊹ Γ2 ≡ Γ
            → Δ1 ⊹ Δ2 ≡ (Δₗ ++ Δᵣ)
            → xs ++ ys ≡ Δ1
            → x ∉ dom (Γ ++ Δₗ ++ Δᵣ)
            → x ∉ dom Γ1 ++ dom Γ2 ++ dom (xs ++ ys)
    -- .

-- . other propositions.

∈-tail : ∀ {A : Set} {y x : A} {xs} → ¬ (y ≡ x) → y ∈ (x ∷ xs) → y ∈ xs
∈-tail {A} {y} {x} {xs} ¬y≡x (here y≡x) = ⊥-elim (¬y≡x y≡x)
∈-tail {A} {y} {x} {xs} ¬y≡x (there y∈xs) = y∈xs

∉→¬≡ : ∀ {A : Set} {x y : A} {L : List A} → y ∉ (x ∷ L) → ¬ (y ≡ x)
∉→¬≡ y∉x∷L refl = y∉x∷L (here refl)

¬≡-sym : ∀ {A : Set} {x y : A} → ¬ (x ≡ y) → ¬ (y ≡ x)
¬≡-sym ¬x≡y refl = ¬x≡y refl

-- .
