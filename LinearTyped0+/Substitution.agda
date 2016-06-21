module Substitution where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List

open import Data.Empty

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Expr
open import Types

-- variable opening --
{- #########################
    [ n ↦ u ] t ≡ replacing
        every `bv n` :: Fin n
        within `t` :: Expr n+1 ≡ Fin n+1
        by `u` :: Fin n
############################ -}

[_↦_] : ∀ n → Expr n → Expr (suc n) → Expr n
[ n ↦ u ] (bv i) with n ≟ℕ toℕ i
[ n ↦ u ] (bv i) | yes n=i = u
[ n ↦ u ] (bv i) | no  n≠i = bv (↓fin i n≠i)
-- .
[ n ↦ u ] (ƛ t) =
    --   (ƛ t) : Expr (n+1)
    -- ⇒ t : Expr (n+2)
    -- ⇒ ?0 must be n+1 for computing [ ?0 ↦ ?1 ] t
    -- ⇒ ?0 = n+1 → ?1 must has type as Expr (n+1)
    ƛ ([ suc n ↦ ↑expr u ] t)
-- .
[ n ↦ u ] (num x) = num x
-- [ n ↦ u ] (fv x) = ↓expr fv x
-- 不需要 ↓expr, 因為 x 會被以新的 type (以及其對應的 constructors來)重構
[ n ↦ u ] (fv x) = fv x
-- .
[ n ↦ u ] (t · t₁) = [ n ↦ u ] t · [ n ↦ u ] t₁
[ n ↦ u ] (! t) = ! [ n ↦ u ] t
[ n ↦ u ] (ask t be! t₁ then t₂) =
    ask [ n ↦ u ] t be! [ n ↦ u ] t₁ then [ n ↦ u ] t₂
[ n ↦ u ] ⟨ t × t₁ ⟩ = ⟨ [ n ↦ u ] t × [ n ↦ u ] t₁ ⟩
[ n ↦ u ] (fst t) = fst ([ n ↦ u ] t)
[ n ↦ u ] (snd t) = snd ([ n ↦ u ] t)
[ n ↦ u ] ⟨ t ∣ t₁ ⟩ = ⟨ [ n ↦ u ] t ∣ [ n ↦ u ] t₁ ⟩
[ n ↦ u ] (ask t be⟨ t₁ ∣ t₂ ⟩then t₃) =
    ask [ n ↦ u ] t be⟨ [ n ↦ u ] t₁ ∣ [ n ↦ u ] t₂ ⟩then [ n ↦ u ] t₃
[ n ↦ u ] (inl t) = inl ([ n ↦ u ] t)
[ n ↦ u ] (inr t) = inr ([ n ↦ u ] t)
[ n ↦ u ] (match t of t₁ ⇒ t₂ or t₃ ⇒ t₄) =
    match [ n ↦ u ] t of
        [ n ↦ u ] t₁ ⇒ [ n ↦ u ] t₂ or
        [ n ↦ u ] t₃ ⇒ [ n ↦ u ] t₄

_₀↦_ : Expr 1 → Expr 0 → Expr 0
m ₀↦ t = [ 0 ↦ t ] m

-- variable closing

[_↤_] : ∀ n → FName → Expr n → Expr (suc n)
[ n ↤ name ] (num x) = num x
[ n ↤ name ] (bv i) = bv i -- 拿掉 ↑expr, 同理如上
-- .
[ n ↤ name ] (fv x) with name ≟S x
[ n ↤ name ] (fv x) | yes p = bv (fromℕ n) -- fromℕ : (n : ℕ) → Fin (suc n)
[ n ↤ name ] (fv x) | no ¬p = ↑expr (fv x)
-- .
[ n ↤ name ] (ƛ t) = ƛ ([ suc n ↤ name ] t)
-- .
[ n ↤ name ] (t · t₁) = [ n ↤ name ] t · [ n ↤ name ] t₁
[ n ↤ name ] (! t) = ! [ n ↤ name ] t
[ n ↤ name ] (ask t be! t₁ then t₂) =
    ask [ n ↤ name ] t be! [ n ↤ name ] t₁ then [ n ↤ name ] t₂
[ n ↤ name ] ⟨ t × t₁ ⟩ = ⟨ [ n ↤ name ] t × [ n ↤ name ] t₁ ⟩
[ n ↤ name ] (fst t) = fst ([ n ↤ name ] t)
[ n ↤ name ] (snd t) = snd ([ n ↤ name ] t)
[ n ↤ name ] ⟨ t ∣ t₁ ⟩ = ⟨ [ n ↤ name ] t ∣ [ n ↤ name ] t₁ ⟩
[ n ↤ name ] (ask t be⟨ t₁ ∣ t₂ ⟩then t₃) =
    ask [ n ↤ name ] t be⟨ [ n ↤ name ] t₁ ∣ [ n ↤ name ] t₂ ⟩then [ n ↤ name ] t₃
[ n ↤ name ] (inl t) = inl ([ n ↤ name ] t)
[ n ↤ name ] (inr t) = inr ([ n ↤ name ] t)
[ n ↤ name ] (match t of t₁ ⇒ t₂ or t₃ ⇒ t₄) =
    match [ n ↤ name ] t of
        [ n ↤ name ] t₁ ⇒ [ n ↤ name ] t₂ or
        [ n ↤ name ] t₃ ⇒ [ n ↤ name ] t₄

close : ∀ {n} → FName → Expr n → Expr (suc n)
close {n} name t = [ n ↤ name ] t

_₀↤_ : Expr 0 → FName → Expr 1
t ₀↤ x = [ 0 ↤ x ] t

-- free variable substitution

[_↝_] : ∀ {n} → FName → Expr n → Expr n → Expr n
[ fn ↝ t ] (num x) = num x
[ fn ↝ t ] (fv x) with fn ≟S x
[ fn ↝ t ] (fv x) | yes p = t
[ fn ↝ t ] (fv x) | no ¬p = fv x
[ fn ↝ t ] (bv i) = bv i
[ fn ↝ t ] (ƛ x) = ƛ ([ fn ↝ ↑expr t ] x) -- +1...
[ fn ↝ t ] (x · x₁) = [ fn ↝ t ] x · [ fn ↝ t ] x₁
[ fn ↝ t ] (! x) = ! [ fn ↝ t ] x
[ fn ↝ t ] (ask x be! x₁ then x₂) =
    ask [ fn ↝ t ] x be! [ fn ↝ t ] x₁ then [ fn ↝ t ] x₂
[ fn ↝ t ] ⟨ x × x₁ ⟩ = ⟨ [ fn ↝ t ] x × [ fn ↝ t ] x₁ ⟩
[ fn ↝ t ] (fst x) = fst ([ fn ↝ t ] x)
[ fn ↝ t ] (snd x) = snd ([ fn ↝ t ] x)
[ fn ↝ t ] ⟨ x ∣ x₁ ⟩ = ⟨ [ fn ↝ t ] x ∣ [ fn ↝ t ] x₁ ⟩
[ fn ↝ t ] (ask x be⟨ x₁ ∣ x₂ ⟩then x₃) =
    ask [ fn ↝ t ] x be⟨ [ fn ↝ t ] x₁ ∣ [ fn ↝ t ] x₂ ⟩then [ fn ↝ t ] x₃
[ fn ↝ t ] (inl x) = inl ([ fn ↝ t ] x)
[ fn ↝ t ] (inr x) = inr ([ fn ↝ t ] x)
[ fn ↝ t ] (match x of x₁ ⇒ x₂ or x₃ ⇒ x₄) =
    match [ fn ↝ t ] x of
        [ fn ↝ t ] x₁ ⇒ [ fn ↝ t ] x₂ or
        [ fn ↝ t ] x₃ ⇒ [ fn ↝ t ] x₄





-- .
