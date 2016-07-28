module Structural where
-- .
open import Data.String renaming (_++_ to _++S_)
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

postulate
    ∉-list-weakenᵣ : ∀ {A : Set} {z : A} {xs : List A} {ys : List A} → z ∉ xs ++ ys → z ∉ xs
    ∉-list-weakenₗ : ∀ {A : Set} {z : A} {xs : List A} {ys : List A} → z ∉ xs ++ ys → z ∉ ys

⊢-weaken : ∀ Γₗ Γᵣ Δₗ Δᵣ x A {t T}
        → x ∉ dom (Γₗ ++ Γᵣ ++ Δₗ ++ Δᵣ)
        → (Γₗ ++ Γᵣ) , (Δₗ              ++ Δᵣ) ⊢ t ∶ T
        → (Γₗ ++ Γᵣ) , (Δₗ ++ [(x , A)] ++ Δᵣ) ⊢ t ∶ T
⊢-weaken = {!   !}
