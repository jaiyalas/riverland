module MayUseful where
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
open import Ctx
-- .
沒有 : (fs : FNames)
    → (x : FName)
    → Dec (x ∉ fs)
沒有 [] x = yes (λ ())
沒有 (f ∷ fs) x with 沒有 fs x
沒有 (f ∷ fs) x | yes p with x ≟S f
沒有 (f ∷ fs) x | yes p | yes x≟f = no (λ x₁ → x₁ (here x≟f))
沒有 (f ∷ fs) x | yes p | no ¬x≟f = yes (λ x₁ → p (Any.tail ¬x≟f x₁))
沒有 (f ∷ fs) x | no ¬p = no (λ x₁ → ¬p (λ x₂ → x₁ (there x₂)))
-- .
沒交集 : (fs : FNames)
    → (xs : FNames)
    → Dec (All.All (λ x → x ∉ fs) xs)
沒交集 fs [] = yes []
沒交集 fs (x ∷ xs) with 沒交集 fs xs
沒交集 fs (x ∷ xs) | yes p with 沒有 fs x
沒交集 fs (x ∷ xs) | yes p | yes 沒x = yes ((λ x₁ → 沒x x₁) ∷ p)
沒交集 fs (x ∷ xs) | yes p | no  有x = no (λ x₁ → 有x (head x₁))
沒交集 fs (x ∷ xs) | no ¬p = no (λ x₁ → ¬p (All.tail x₁) )
-- .
checkFVs : ∀ {n} → Ctx → Expr n → Set
checkFVs Γ t = All.All (λ x → x ∉ (Data.List.map proj₁ Γ)) (fvars t)
--
-- .
{-
The oiginal distinct domain is no longer suit the situiation
since we will use the dual contexts for
inituistionistic and lina logic

Therefore we at least should *product* two domains as one.
-}

namespace- : ∀ {A} → Assoc FName A → Assoc FName A → FNames
namespace- xs ys = Data.List.map proj₁ xs ++ Data.List.map proj₁ ys

data DualDom {A : Set} : (Assoc FName A) × (Assoc FName A) → Set where
    none : DualDom ([] , [])
    pure : ∀ {Γ [Γ] A}
        → (x : FName)
        → (x∉ : x ∉ namespace- Γ [Γ])
        → DualDom (Γ , [Γ])
        → DualDom ((x , A) ∷ Γ , [Γ])
    bang : ∀ {Γ [Γ] A}
        → (x : FName)
        → (x∉ : x ∉ namespace- Γ [Γ])
        → DualDom (Γ , [Γ])
        → DualDom (Γ , (x , A) ∷ [Γ])

namespace : ∀ {Γ Δ : Assoc FName LType} → DualDom (Γ , Δ) → FNames
namespace none = []
namespace (pure x x∉ ddom) = x ∷ namespace ddom
namespace (bang x x∉ ddom) = x ∷ namespace ddom
-- .
