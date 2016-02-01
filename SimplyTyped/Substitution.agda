module Substitution where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List

open import Data.Empty

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Expr

-- variable opening

[_↦_] : ∀ n → Expr n → Expr (suc n) → Expr n
[ m ↦ t ] (num i) = num i
[ m ↦ t ] (bv i) with m ≟ℕ toℕ i
... | yes m=i = t
... | no  m≠i = bv (↓fin i m≠i) -- (↓fin i m≠i)
[ m ↦ t ] (fv x) = fv x
[ m ↦ t ] (ƛ τ e) = ƛ τ ([ suc m ↦ ↑expr t ] e)
[ m ↦ t ] (f · e) = [ m ↦ t ] f · [ m ↦ t ] e
[ m ↦ t ] ⟨ x , y ⟩ = ⟨ [ m ↦ t ] x , [ m ↦ t ] y ⟩
[ m ↦ t ] (fst e) = fst ([ m ↦ t ] e)
[ m ↦ t ] (snd e) = snd ([ m ↦ t ] e)
[ m ↦ t ] (inl e) = inl ([ m ↦ t ] e)
[ m ↦ t ] (inr e) = inr ([ m ↦ t ] e)
[ m ↦ t ] (match x of a ⟩ x₁ or b ⟩ x₂ ) =
   match [ m ↦ t ] x of
      [ m ↦ t ] a ⟩ [ m ↦ t ] x₁ or
      [ m ↦ t ] b ⟩ [ m ↦ t ] x₂

_₀↦_ : Expr 1 → Expr 0 → Expr 0
m ₀↦ t = [ 0 ↦ t ] m

-- variable closing

[_↤_] : ∀ n → FName → Expr n → Expr (suc n)
[ m ↤ name ] (num x) = num x
[ m ↤ name ] (fv x) with name ≟S x
[ m ↤ name ] (fv x) | yes p = bv (fromℕ m)
[ m ↤ name ] (fv x) | no ¬p = fv x
[ m ↤ name ] (bv i) = bv (suc i)
[ m ↤ name ] (ƛ τ e) = ƛ τ (↑expr e)
[ m ↤ name ] (f · e) = [ m ↤ name ] f · [ m ↤ name ] e
[ m ↤ name ] ⟨ e₁ , e₂ ⟩ = ⟨ [ m ↤ name ] e₁ , [ m ↤ name ] e₂ ⟩
[ m ↤ name ] (fst e) = fst ([ m ↤ name ] e)
[ m ↤ name ] (snd e) = snd ([ m ↤ name ] e)
[ m ↤ name ] (inl e) = inl ([ m ↤ name ] e)
[ m ↤ name ] (inr e) = inr ([ m ↤ name ] e)
[ m ↤ name ] (match x of a ⟩ x₁ or b ⟩ x₂ ) =
   match [ m ↤ name ] x of
      [ m ↤ name ] a ⟩ [ m ↤ name ] x₁ or
      [ m ↤ name ] b ⟩ [ m ↤ name ] x₂

_₀↤_ : Expr 0 → FName → Expr 1
t ₀↤ x = [ 0 ↤ x ] t

-- free variable substitution

[_↝_] : ∀ {n} → FName → Expr n → Expr n → Expr n
[ fn ↝ t ] (num x) = num x
[ fn ↝ t ] (fv x) with fn ≟S x
[ fn ↝ t ] (fv x) | yes p = t
[ fn ↝ t ] (fv x) | no ¬p = fv x
[ fn ↝ t ] (bv i) = bv i
[ fn ↝ t ] (ƛ τ e) = ƛ τ ([ fn ↝ ↑expr t ] e)
[ fn ↝ t ] (e · e₁) = [ fn ↝ t ] e · [ fn ↝ t ] e₁
[ fn ↝ t ] ⟨ e , e₁ ⟩ = ⟨ [ fn ↝ t ] e , [ fn ↝ t ] e₁ ⟩
[ fn ↝ t ] (fst e) = fst ([ fn ↝ t ] e)
[ fn ↝ t ] (snd e) = snd ([ fn ↝ t ] e)
[ fn ↝ t ] (inl e) = inl ([ fn ↝ t ] e)
[ fn ↝ t ] (inr e) = inr ([ fn ↝ t ] e)
[ fn ↝ t ] (match x of a ⟩ x₁ or b ⟩ x₂ ) =
   match [ fn ↝ t ] x of
      [ fn ↝ t ] a ⟩ [ fn ↝ t ] x₁ or
      [ fn ↝ t ] b ⟩ [ fn ↝ t ] x₂







-- .
