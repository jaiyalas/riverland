module Substitution where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List

open import Data.Empty

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Expr

[_↦_] : ∀ n → Expr n → Expr (suc n) → Expr n
[ m ↦ t ] (num i) = num i
[ m ↦ t ] (bv i) with m ≟ℕ toℕ i
... | yes m=i = t
... | no  m≠i = bv (↓fin i m≠i)
[ m ↦ t ] (fv x) = fv x
[ m ↦ t ] (ƛ e) = ƛ ([ suc m ↦ ↑expr t ] e)
[ m ↦ t ] (e · e₁) = [ m ↦ t ] e · [ m ↦ t ] e₁

[_↤_] : ∀ n → FName → Expr n → Expr (suc n)
[ m ↤ name ] (num x)  = num x
[ m ↤ name ] (bv i)   = ↑expr (bv i)
[ m ↤ name ] (fv x)   with x ≟S name
[ m ↤ name ] (fv x) | yes p = bv (fromℕ m)
[ m ↤ name ] (fv x) | no ¬p = fv x
[ m ↤ name ] (ƛ t)    = ƛ ([ suc m ↤ name ] t)
[ m ↤ name ] (t · t₁) = [ m ↤ name ] t · [ m ↤ name ] t₁

[_↝_] : ∀ {n} → FName → Expr n → Expr n → Expr n
[ n ↝ t ] (num i) = num i
[ n ↝ t ] (bv i) = bv i
[ n ↝ t ] (fv x) with n ≟S x
[ n ↝ t ] (fv x) | yes p = t
[ n ↝ t ] (fv x) | no ¬p = fv x
[ n ↝ t ] (ƛ x) = ƛ ([ n ↝ ↑expr t ] x)
[ n ↝ t ] (x · y) = [ n ↝ t ] x · [ n ↝ t ] y

_₀↦_ : Expr 1 → Expr 0 → Expr 0
m ₀↦ t = [ 0 ↦ t ] m

_↦₀_ : FName → Expr 0 → Expr 1
name ↦₀ t = [ 0 ↤ name ] t

_₀↤_ : Expr 0 → FName → Expr 1
t ₀↤ x = [ 0 ↤ x ] t

_₀↝_ : Expr 1 → FName → Expr 0
x ₀↝ s = x ₀↦ (fv s)

phantomName : ∀ {nn} {e} → nn ↦₀ (e ₀↦ fv nn) ≡ e
phantomName = {!   !}





--
