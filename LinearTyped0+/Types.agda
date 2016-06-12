module Types where

open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any

-- ##### newtype ##### --

Assoc : Set → Set → Set
Assoc A B = List (A × B)

FName : Set
FName = String

FNames : Set
FNames = List FName

-- ##### Type ##### --

data IType : Set where
   numᵗ : IType
   _⊃_ : IType → IType → IType
   _∧_ : IType → IType → IType
   _∨_ : IType → IType → IType

data LType : Set where
   numᵗ : LType
   _⊸_  : LType → LType → LType
   _⊕_  : LType → LType → LType
   _⊗_  : LType → LType → LType
   _&_  : LType → LType → LType
   ⟪_⟩  : LType → LType
