module Structural where
-- .
open import Data.Product using (∃; _,_; proj₁)
open import Data.Sum
-- open import Data.Product hiding (map)
-- open import Data.Bool using (not)
open import Data.String renaming (_++_ to _++S_; _≟_ to _≟S_)
open import Data.List
open import Data.List.Any as Any
open import Data.List.All as All
open Any.Membership-≡ using (_∈_; _∉_)
open import Relation.Nullary using (¬_; yes; no)
-- .
open import Types
open import Expr
open import FVar
open import Ctx
open import Substitution
open import Typing
-- .

-- .
⊢-weaken : ∀ Γ Δₗ Δᵣ x A {t T}
        → x ∉ dom (Γ ++ Δₗ ++ Δᵣ)
        → Γ , (Δₗ              ++ Δᵣ) ⊢ t ∶ T
        → Γ , (Δₗ ++ [(x , A)] ++ Δᵣ) ⊢ t ∶ T
-- .
⊢-weaken Γ Δₗ Δᵣ x A {num x₁} x∉ctx litℕ = litℕ
⊢-weaken Γ Δₗ Δᵣ x A {fv x₁} x∉ctx (var ddd x₁∈Γ) =
    var (DDD-insert Γ Δₗ Δᵣ x ddd x∉ctx) x₁∈Γ
⊢-weaken Γ Δₗ Δᵣ x A {fv x₁} x∉ctx (var! ddd x₁∈Δ) =
    var! (DDD-insert Γ Δₗ Δᵣ x ddd x∉ctx) (∈-++-weaken Δₗ ([ (x , A) ]) Δᵣ x₁∈Δ)
⊢-weaken Γ Δₗ Δᵣ x A {bv i} x∉ctx ()
⊢-weaken Γ Δₗ Δᵣ x A {ƛ t} x∉ctx (⊸-I ctx {A = A2} t[∀z/n]) =
    ⊸-I (x ∷ ctx)
        (λ y y∉x∷ctx →
            ⊢-weaken ((y , A2) ∷ Γ) Δₗ Δᵣ x A
                -- x∉y∷ctx
                (λ x∈y∷ctx → x∉ctx (∈-tail (¬≡-sym (∉-¬≡ y∉x∷ctx)) x∈y∷ctx))
                -- t[y/n] ; y∉ctx
                (t[∀z/n] y (λ y∈ctx → y∉x∷ctx (there y∈ctx))))
⊢-weaken Γ Δₗ Δᵣ x A {t · t₁} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {bang t} x∉ctx (‼-I x₁ p) =
    ‼-I (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx x₁) p
⊢-weaken Γ Δₗ Δᵣ x A {ask t be!then t₁} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {⟨ t ∣ t₁ ⟩} x∉ctx (&-I p p₁) =
    &-I (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p) (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p₁)
⊢-weaken Γ Δₗ Δᵣ x A {⟨ t × t₁ ⟩} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {ask t be⟨×⟩then t₁} x∉ctx p = {! p   !}
⊢-weaken Γ Δₗ Δᵣ x A {inl t} x∉ctx (⊕-I₁ p) = ⊕-I₁ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
⊢-weaken Γ Δₗ Δᵣ x A {inr t} x∉ctx (⊕-I₂ p) = ⊕-I₂ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
⊢-weaken Γ Δₗ Δᵣ x A {match t of t₁ or t₂} x∉ctx p = {! p   !}
⊢-weaken Γ Δₗ Δᵣ x A {fst t} {T} x∉ctx (&-E₁ p) =
    &-E₁ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
⊢-weaken Γ Δₗ Δᵣ x A {snd t} x∉ctx (&-E₂ p) =
    &-E₂ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
-- .

-- .
⊢-exchange : ∀ Γ1 Γ2 Δ1 Δ2 {t T}
    → (Γ1 ++ Γ2) , (Δ1 ++ Δ2) ⊢ t ∶ T
    → (Γ2 ++ Γ1) , (Δ2 ++ Δ1) ⊢ t ∶ T
⊢-exchange Γ1 Γ2 Δ1 Δ2 p = {! p  !}
-- .

-- .
⊢-contr : ∀ Γ Δ1 Δ2 x y z A {t T}
    → Γ , (Δ1 ++ (x , A) ∷ (y , A) ∷ Δ2) ⊢ t ∶ T
    → Γ , (Δ1 ++ (z , A) ∷ Δ2) ⊢ [ y ↝ fv z ] ([ x ↝ fv z ] t) ∶ T
⊢-contr Γ Δ1 Δ2 x y z A p = {! p  !}

-- .
