module Structural where
-- .
-- open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; _,_)
-- open import Data.Product hiding (map)
-- open import Data.Bool using (not)
-- open import Data.String using (_==_)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)
-- .
open import Expr
open import Types
open import Substitution
open import Typing

-- ----------------------
-- ## structural rules ##
-- ----------------------
exchange : ∀ Γ [Γ] Δ [Δ] {t B}
    → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ t ∶ B
    → (Δ ++ Δ) , ([Δ] ++ [Γ]) ⊢ t ∶ B
exchange Γ [Γ] Δ [Δ] x = {! x  !}
-- contraction
-- weakening
-- weakening : ∀ L Γ [Γ] nfn T {t B}
--     → nfn ∉ DomDist (Γ ++ [Γ])
--     → Γ ,             [Γ] ⊢ t ∶ B
--     → Γ , (nfn , T) ∷ [Γ] ⊢ t ∶ B
-- .
-- .
