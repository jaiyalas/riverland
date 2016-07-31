module Structural where
-- .
open import Data.String renaming (_++_ to _++S_; _≟_ to _≟S_)
open import Data.Product using (∃; _,_; proj₁)
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

postulate
    leftFree : ∀ {A : Set} {z : A} {xs : List A} {ys : List A} → z ∉ xs ++ ys → z ∉ xs
    rightFree : ∀ {A : Set} {z : A} {xs : List A} {ys : List A} → z ∉ xs ++ ys → z ∉ ys

-- 1. x ∉ fvars t ⇒ x ∉ Γ ⊎ Δ
-- 2. x ∷ xs ⇒ ls ++ x ++ rs
-- .
⊢-weaken : ∀ Γ Δ t T x A → x ∉ fvars t → Γ , Δ ⊢ t ∶ T → Γ , (x , A) ∷ Δ ⊢ t ∶ T
⊢-weaken Γ Δ (num x) .Num x₁ A x∉t litℕ = litℕ
⊢-weaken Γ Δ (fv n) T x A x∉t (var x₂ x₃) = var x₂ x₃
⊢-weaken Γ Δ (fv n) T x A x∉t (var! DDΔ nt∈Δ) = var! DDx∷Δ (there nt∈Δ)
    where DDx∷Δ = rightFree {xs = Data.List.map proj₁ Γ} {! x∉t  !} ∷ DDΔ
⊢-weaken Γ Δ (bv i) T x A x∉t ()
-- .
⊢-weaken Γ Δ (ƛ t) ._ x A x∉t (⊸-I L x₁) = ⊸-I (x ∷ L) {!   !}
⊢-weaken ._ ._ (t · t₁) T x A x∉t (⊸-E h h₁) =
    {!   !}
-- .
⊢-weaken .[] Δ (! t) ._ x A x∉t (‼-I {A = A2} h) = ‼-I (⊢-weaken [] Δ t A2 x A x∉t h)
⊢-weaken ._ ._ (ask t be!then t₁) T x A x∉t (‼-E L h x₁) =
    {!   !}
-- .
⊢-weaken Γ Δ ⟨ tl ∣ tr ⟩ ._ x A x∉t (&-I {A = A2} {B = B2} hl hr) = &-I
    (⊢-weaken Γ Δ tl A2 x A (leftFree x∉t) hl)
    (⊢-weaken Γ Δ tr B2 x A (rightFree {xs = fvars tl} x∉t) hr)
⊢-weaken Γ Δ (fst t) T x A x∉t (&-E₁ {B = B2} h) = &-E₁ (⊢-weaken Γ Δ t (T & B2) x A x∉t h)
⊢-weaken Γ Δ (snd t) T x A x∉t (&-E₂ {A = A2} h) = &-E₂ (⊢-weaken Γ Δ t (A2 & T) x A x∉t h)
-- .
⊢-weaken ._ ._ ⟨ t × t₁ ⟩ ._ x A x∉t (⊗-I h h₁) =
    {!   !}
⊢-weaken ._ ._ (ask t be⟨×⟩then t₁) T x A x∉t (⊗-E L h x₁) =
    {!   !}
-- .
⊢-weaken Γ Δ (inl t) ._ x A x∉t (⊕-I₁ {A = A2} h) = ⊕-I₁ (⊢-weaken Γ Δ t A2 x A x∉t h)
⊢-weaken Γ Δ (inr t) ._ x A x∉t (⊕-I₂ {B = B2} h) = ⊕-I₂ (⊢-weaken Γ Δ t B2 x A x∉t h)
⊢-weaken ._ ._ (match t of t₁ or t₂) T x A x∉t (⊕-E L h hx hy) =
    {!   !}
