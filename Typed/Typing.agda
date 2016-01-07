module Tying where

open import Exp

Assoc : Set → Set → Set
Assoc A B = List (A × B)

Cxt : Set
Cxt = Assoc FName Ty

data _⊢_∶_ : Cxt → Expr → Typ → Set where
