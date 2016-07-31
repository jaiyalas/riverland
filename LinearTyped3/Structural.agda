module Structural where
-- .
open import Data.Product using (∃; _,_; proj₁)
open import Data.Sum
-- open import Data.Product hiding (map)
-- open import Data.Bool using (not)
-- open import Data.String using (_==_)
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

{-
I'm not sure if there should be a case for the constructor ‼-I,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
    [] ≟ Γₗ₁ ++ Γᵣ₁
    Δ ≟ Δₗ₁ ++ Δᵣ₁
    ! t₁ ≟ t
    ‼ A₂ ≟ T
when checking that the expression ? has type
    (Γₗ ++ Γᵣ) , Δₗ ++ [ x , A ] ++ Δᵣ ⊢ .t ∶ .T
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
I'm not sure if there should be a case for the constructor ‼-E,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
    Γ₂ ++ Γ+ ≟ Γ₁
    Δ ++ Δ+ ≟ Δₗ₁ ++ Δᵣ₁
    ask t₁ be!then u ≟ t
    B ≟ T
when checking that the expression ? has type
    Γ , Δₗ ++ [ x , A ] ++ Δᵣ ⊢ .t ∶ .T

-}

postulate
    ∉-list-weakenᵣ : ∀ {A : Set} {z : A} {xs : List A} {ys : List A} → z ∉ xs ++ ys → z ∉ xs
    ∉-list-weakenₗ : ∀ {A : Set} {z : A} {xs : List A} {ys : List A} → z ∉ xs ++ ys → z ∉ ys
-- .
⊢-weaken : ∀ Γ Δₗ Δᵣ x A {t T}
        → x ∉ dom (Γ ++ Δₗ ++ Δᵣ)
        → Γ , (Δₗ              ++ Δᵣ) ⊢ t ∶ T
        → Γ , (Δₗ ++ [(x , A)] ++ Δᵣ) ⊢ t ∶ T
-- .
⊢-weaken Γ Δₗ Δᵣ x A {num x₁} x∉ctx litℕ = litℕ
⊢-weaken Γ Δₗ Δᵣ x A {fv x₁} x∉ctx (var x₂ x₃) = var {!   !} {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {fv x₁} x∉ctx (var! x₂ x₃) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {bv i} x∉ctx ()
⊢-weaken Γ Δₗ Δᵣ x A {ƛ t} x∉ctx (⊸-I L x₁) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {t · t₁} {T} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {bang t} x∉ctx (‼-I x₁ p) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {ask t be!then t₁} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {⟨ t ∣ t₁ ⟩} x∉ctx (&-I p p₁) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {fst t} x∉ctx (&-E₁ p) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {snd t} x∉ctx (&-E₂ p) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {⟨ t × t₁ ⟩} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {ask t be⟨×⟩then t₁} x∉ctx p = {! p   !}
⊢-weaken Γ Δₗ Δᵣ x A {inl t} x∉ctx (⊕-I₁ p) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {inr t} x∉ctx (⊕-I₂ p) = {!   !}
⊢-weaken Γ Δₗ Δᵣ x A {match t of t₁ or t₂} x∉ctx p = {! p   !}





-- .
