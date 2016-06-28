module Types where

open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

-- ##### free name and context ##### --

FName : Set
FName = String

FNames : Set
FNames = List FName

-- ##### Type ##### --

-- intuitionistic type
data IType : Set where
    -- primitive natural number
    Num : IType
    -- function type
    _⊃_ : IType → IType → IType
    -- product type
    _∧_ : IType → IType → IType
    -- sum type
    _∨_ : IType → IType → IType


data LType : Set where
    -- primitive natural number
    Num : LType
    -- linear function type
    -- EAGER!
    _⊸_  : LType → LType → LType

    -- Simultaneous Conjunction
    -- tensor product
    -- EAGER!
    _⊗_  : LType → LType → LType

    -- Alternative Conjunction
    -- direct product
    -- 直積, 真的要都有
    -- LAZY!
    _&_  : LType → LType → LType

    -- Simultaneous Disjunction
    -- tensor sum
    -- _⅋_  : LType → LType → LType

    -- Alternative Disjunction
    -- direct sum
    -- EAGER!
    _⊕_  : LType → LType → LType

    -- of course
    -- LAZY!
    ⟪_⟫  : LType → LType

    -- why not
    -- ⁇_⁇ : LType → LType

    -- linear negation
    -- ¬ : LType → LType

    -- unit and zero
    -- 0ₜ : LType
    -- 1ₜ : LType

    -- top and bottom
    -- ⊤ₜ : LType
    -- ⊥ₜ : LType

-- ##### free name and context ##### --

Assoc : Set → Set → Set
Assoc A B = List (A × B)

Ctx : Set
Ctx = Assoc FName LType

CtxI : Set
CtxI = Assoc FName IType

-- ##### distinct domain ##### --
-- for avoiding the variable name collision
-- will be useful later
data DomDist {A : Set} : Assoc FName A → Set where
    [] : DomDist []
    _∷_ : ∀ {Γ x τ}
         → (x∉ : x ∉ (Data.List.map proj₁ Γ))
         → DomDist Γ
         → DomDist ((x , τ) ∷ Γ)

-- .
