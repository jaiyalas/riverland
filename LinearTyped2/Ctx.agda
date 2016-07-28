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
-- . 果然還是要 dual dist domain 
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
