module Reduction where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)

open import Expr
open import Substitution

-- ############################## --
{-       value and semantics      -}
-- ############################## --

data Val : Expr 0 → Set where
   num⁰ : ∀ n → Val (num n)
   ƛ⁰   : ∀ e → Val (ƛ e)

var? : (e : Expr 0) → (Val e ⊎ ¬ (Val e))
var? (num i) = inj₁ (num⁰ i)
var? (bv i) = inj₂ (λ ())
var? (fv x) = inj₂ (λ ())
var? (ƛ x) = inj₁ (ƛ⁰ x)
var? (x · y) = inj₂ (λ ())

-- don't know what the hell this shit is
data _⟼_ : Expr 0 → Expr 0 → Set where
   app : ∀ {body para}
       → ((ƛ body) · para) ⟼ (body ₀↦ para)
