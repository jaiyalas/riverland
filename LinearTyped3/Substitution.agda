module Substitution where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)

open import Relation.Nullary using (¬_; yes; no)

open import Expr
open import Types

-- #################################### --
-- the outermost bound variable opening --
-- #################################### --

[_↦_] : ∀ (n : ℕ) → Expr n → Expr (suc n) → Expr n
[ n ↦ u ] (bv i) with n ≟ℕ toℕ i
[ n ↦ u ] (bv i) | yes n=i = u
[ n ↦ u ] (bv i) | no  n≠i = bv (↓fin i n≠i)
[ n ↦ u ] (ƛ t) = ƛ ([ suc n ↦ ↑expr u ] t)
-- .
[ n ↦ u ] (num x) = num x
[ n ↦ u ] (fv x) = fv x
-- .
[ n ↦ u ] (t · t₁) = [ n ↦ u ] t · [ n ↦ u ] t₁
[ n ↦ u ] (bang t) = bang [ n ↦ u ] t
[ n ↦ u ] (ask x be!then t) =
    ask [ n ↦ u ] x be!then [ suc n ↦ ↑expr u ] t
[ n ↦ u ] ⟨ t ∣ t₁ ⟩ = ⟨ [ n ↦ u ] t ∣ [ n ↦ u ] t₁ ⟩
[ n ↦ u ] (fst t) = fst ([ n ↦ u ] t)
[ n ↦ u ] (snd t) = snd ([ n ↦ u ] t)
[ n ↦ u ] ⟨ f × g ⟩ = ⟨ [ n ↦ u ] f × [ n ↦ u ] g ⟩
[ n ↦ u ] (ask x be⟨×⟩then t) =
    ask [ n ↦ u ] x be⟨×⟩then [ suc (suc n) ↦ ↑expr (↑expr u) ] t
[ n ↦ u ] (inl t) = inl ([ n ↦ u ] t)
[ n ↦ u ] (inr t) = inr ([ n ↦ u ] t)
[ n ↦ u ] (match t of f or g) =
    match [ n ↦ u ] t of [ suc n ↦ ↑expr u ] f or [ suc n ↦ ↑expr u ] g

-- #################################### --
-- the outermost bound variable closing --
-- #################################### --

[_↤_] : ∀ n → FName → Expr n → Expr (suc n)
[ n ↤ name ] (fv x) with name ≟S x
[ n ↤ name ] (fv x) | yes p = bv (fromℕ n)
[ n ↤ name ] (fv x) | no ¬p = fv x
-- .
[ n ↤ name ] (ƛ t) = ƛ ([ suc n ↤ name ] t)
-- .
[ n ↤ name ] (num x) = num x
[ n ↤ name ] (bv i) = ↑bv (bv i)
-- .
[ n ↤ name ] (t · t₁) = [ n ↤ name ] t · [ n ↤ name ] t₁
[ n ↤ name ] (bang t) = bang [ n ↤ name ] t
[ n ↤ name ] (ask t be!then f) =
    ask [ n ↤ name ] t be!then [ suc n ↤ name ] f
[ n ↤ name ] ⟨ f ∣ g ⟩ = ⟨ [ n ↤ name ] f ∣ [ n ↤ name ] g ⟩
[ n ↤ name ] (fst t) = fst ([ n ↤ name ] t)
[ n ↤ name ] (snd t) = snd ([ n ↤ name ] t)
[ n ↤ name ] ⟨ f × g ⟩ = ⟨ [ n ↤ name ] f × [ n ↤ name ] g ⟩
[ n ↤ name ] (ask t be⟨×⟩then f) =
    ask [ n ↤ name ] t be⟨×⟩then [ suc (suc n) ↤ name ] f
[ n ↤ name ] (inl t) = inl ([ n ↤ name ] t)
[ n ↤ name ] (inr t) = inr ([ n ↤ name ] t)
[ n ↤ name ] (match t of f or g) =
    match [ n ↤ name ] t of [ suc n ↤ name ] f or [ suc n ↤ name ] g
-- .

-- free variable substitution

[_↝_] : ∀ {n} → FName → Expr n → Expr n → Expr n
[ fn ↝ t ] (num x) = num x
[ fn ↝ t ] (fv x) with fn ≟S x
[ fn ↝ t ] (fv x) | yes p = t
[ fn ↝ t ] (fv x) | no ¬p = fv x
[ fn ↝ t ] (bv i) = bv i
[ fn ↝ t ] (ƛ x) = ƛ ([ fn ↝ ↑expr t ] x)
[ fn ↝ t ] (x · x₁) = [ fn ↝ t ] x · [ fn ↝ t ] x₁
[ fn ↝ t ] (bang x) = bang [ fn ↝ t ] x
[ fn ↝ t ] (ask x be!then f) =
    ask [ fn ↝ t ] x be!then [ fn ↝ ↑expr t ] f
[ fn ↝ t ] ⟨ x ∣ x₁ ⟩ = ⟨ [ fn ↝ t ] x ∣ [ fn ↝ t ] x₁ ⟩
[ fn ↝ t ] (fst x) = fst ([ fn ↝ t ] x)
[ fn ↝ t ] (snd x) = snd ([ fn ↝ t ] x)
[ fn ↝ t ] ⟨ x × x₁ ⟩ = ⟨ [ fn ↝ t ] x × [ fn ↝ t ] x₁ ⟩
[ fn ↝ t ] (ask x be⟨×⟩then f) =
    ask [ fn ↝ t ] x be⟨×⟩then [ fn ↝ ↑expr (↑expr t) ] f
[ fn ↝ t ] (inl x) = inl ([ fn ↝ t ] x)
[ fn ↝ t ] (inr x) = inr ([ fn ↝ t ] x)
[ fn ↝ t ] (match x of f or g) =
    match [ fn ↝ t ] x of [ fn ↝ ↑expr t ] f or [ fn ↝ ↑expr t ] g

bv-opening : ∀ {n} → Expr (suc n) → Expr n → Expr n
bv-opening {n} t s = [ n ↦ s ] t

bv-closing : ∀ {n} → Expr n → FName → Expr (suc n)
bv-closing {n} t name = [ n ↤ name ] t

-- .
