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

-- #################################### --
-- the outermost bound variable opening --
-- #################################### --
-- 把 Expr (suc n) 裡面最大的 (bv i) {where i=n} 給換成某個  Expr n 的玩意
-- [interpretation 1]
-- 假設 t : Expr (suc n) 沒有浮報 {i.e. 裡面真的 somewhere 有 (bv n)}
-- [ n ↦ u ] t 會
--     1.把 t 裡面那個最大的 bv 給換成 u; 同時
--     2.把 其他 bv (suc m) 給變成 bv m
[_↦_] : ∀ (n : ℕ) → Expr n → Expr (suc n) → Expr n
[ n ↦ u ] (bv i) with n ≟ℕ toℕ i -- from type info, we know that i ≤ n
[ n ↦ u ] (bv i) | yes n=i =
    -- if `i = n` then direct replacement will do
    u
[ n ↦ u ] (bv i) | no  n≠i =
    -- if `i < n` then we do nothing on the expression
    -- but reduce `bv i` by 1 on its type
    bv (↓fin i n≠i)
[ n ↦ u ] (ƛ t) =
    --   (ƛ t) : Expr (n+1)
    -- ⇒ t : Expr (n+2)
    -- ⇒ [ n+1 ↦ ? : expr n+1 ] t
    -- the problem is, use `↑expr` or `↑bv`
    {-
    given the following example:
    --
    ⟨ ƛ [bv 0, bv 1, bv 2] × [bv 0, bv 1] ⟩ : Expr 2
    --
      [ 1 ↦ ex1 ] ⟨ ƛ [bv 0, bv 1, bv 2] × [bv 0, bv 1] ⟩
    ≡  ⟨ [ 1 ↦ ex1 ] (ƛ [bv 0, bv 1, bv 2]) × [ 1 ↦ ex1 ] [bv 0, bv 1] ⟩
    ≡  ⟨ [ 1 ↦ ex1 ] (ƛ [bv 0, bv 1, bv 2]) × [bv 0, ex1] ⟩
    ≡  ⟨ ƛ ([ 2 ↦ ex2 ] [bv 0, bv 1, bv 2]) × [bv 0, ex1] ⟩

        如果我們只看右手邊, [ 1 ↦ ex1 ] [bv 0, bv 1] : Expr 1
        又 ex1 最多是 bv 0 所以 [ 1 ↦ ex1 ] [bv 0, bv 1] ≡ [bv 0, bv 0]
        而[bv 0, bv 0] 確實可以是 Expr 1

    ≡  ⟨ ƛ ([ 2 ↦ ex2 ] [bv 0, bv 1, bv 2]) × [bv 0, ex1] ⟩
    ≡  ⟨ ƛ [bv 0, bv 1, ex2] × [bv 0, ex1] ⟩

        同理 ex2 最多是 bv 1 所以 [bv 0, bv 1, ex2] ≡ [bv 0, bv 1, bv 1]
        此時 LHS 這裡的 bv 1 和 RHS 的 bv 0 會是指同一個東西

        所以，這裡會是需要 ↑expr 而不是 ↑bv
    -}
    ƛ ([ suc n ↦ ↑expr u ] t)
-- .
[ n ↦ u ] (num x) = num x
[ n ↦ u ] (fv x) = fv x
-- .
[ n ↦ u ] (t · t₁) = [ n ↦ u ] t · [ n ↦ u ] t₁
[ n ↦ u ] (! t) = ! [ n ↦ u ] t
[ n ↦ u ] (ask x be!then t) =
    ask [ n ↦ u ] x be!then [ n ↦ u ] t
[ n ↦ u ] ⟨ t ∣ t₁ ⟩ = ⟨ [ n ↦ u ] t ∣ [ n ↦ u ] t₁ ⟩
[ n ↦ u ] (fst t) = fst ([ n ↦ u ] t)
[ n ↦ u ] (snd t) = snd ([ n ↦ u ] t)
[ n ↦ u ] ⟨ f × g ⟩ = ⟨ [ n ↦ u ] f × [ n ↦ u ] g ⟩
[ n ↦ u ] (ask x be⟨×⟩then t) =
    ask [ n ↦ u ] x be⟨×⟩then [ n ↦ u ] t
[ n ↦ u ] (inl t) = inl ([ n ↦ u ] t)
[ n ↦ u ] (inr t) = inr ([ n ↦ u ] t)
[ n ↦ u ] (match t of f or g) =
    match [ n ↦ u ] t of [ n ↦ u ] f or [ n ↦ u ] g

-- well-bounded(?)
_₀↦_ : Expr 1 → Expr 0 → Expr 0
m ₀↦ t = [ 0 ↦ t ] m

-- #################################### --
-- the outermost bound variable closing --
-- #################################### --

-- [_↤_] : ∀ n → FName → Expr n → Expr (suc n)
-- [ n ↤ name ] (fv x) with name ≟S x
-- [ n ↤ name ] (fv x) | yes p = bv (fromℕ n)
-- [ n ↤ name ] (fv x) | no ¬p = ↑expr (fv x)
-- -- .
-- [ n ↤ name ] (ƛ t) = ƛ ([ suc n ↤ name ] t)
-- -- .
-- [ n ↤ name ] (num x) = num x
-- [ n ↤ name ] (bv i) = bv i
-- -- .
-- [ n ↤ name ] (t · t₁) = [ n ↤ name ] t · [ n ↤ name ] t₁
-- [ n ↤ name ] (! t) = ! [ n ↤ name ] t
-- [ n ↤ name ] (ask t be! t₁ then t₂) =
--     ask [ n ↤ name ] t be! [ n ↤ name ] t₁ then [ n ↤ name ] t₂
-- [ n ↤ name ] ⟨ t × t₁ ⟩ = ⟨ [ n ↤ name ] t × [ n ↤ name ] t₁ ⟩
-- [ n ↤ name ] (fst t) = fst ([ n ↤ name ] t)
-- [ n ↤ name ] (snd t) = snd ([ n ↤ name ] t)
-- [ n ↤ name ] ⟨ t ∣ t₁ ⟩ = ⟨ [ n ↤ name ] t ∣ [ n ↤ name ] t₁ ⟩
-- [ n ↤ name ] (ask t be⟨ t₁ ∣ t₂ ⟩then t₃) =
--     ask [ n ↤ name ] t be⟨ [ n ↤ name ] t₁ ∣ [ n ↤ name ] t₂ ⟩then [ n ↤ name ] t₃
-- [ n ↤ name ] (inl t) = inl ([ n ↤ name ] t)
-- [ n ↤ name ] (inr t) = inr ([ n ↤ name ] t)
-- [ n ↤ name ] (match t of t₁ ⇒ t₂ or t₃ ⇒ t₄) =
--     match [ n ↤ name ] t of
--         [ n ↤ name ] t₁ ⇒ [ n ↤ name ] t₂ or
--         [ n ↤ name ] t₃ ⇒ [ n ↤ name ] t₄
--
-- close : ∀ {n} → FName → Expr n → Expr (suc n)
-- close {n} name t = [ n ↤ name ] t
--
-- _₀↤_ : Expr 0 → FName → Expr 1
-- t ₀↤ x = [ 0 ↤ x ] t

-- free variable substitution

-- [_↝_] : ∀ {n} → FName → Expr n → Expr n → Expr n
-- [ fn ↝ t ] (num x) = num x
-- [ fn ↝ t ] (fv x) with fn ≟S x
-- [ fn ↝ t ] (fv x) | yes p = t
-- [ fn ↝ t ] (fv x) | no ¬p = fv x
-- [ fn ↝ t ] (bv i) = bv i
-- [ fn ↝ t ] (ƛ x) = ƛ ([ fn ↝ ↑expr t ] x) -- +1...
-- [ fn ↝ t ] (x · x₁) = [ fn ↝ t ] x · [ fn ↝ t ] x₁
-- [ fn ↝ t ] (! x) = ! [ fn ↝ t ] x
-- [ fn ↝ t ] (ask x be! x₁ then x₂) =
--     ask [ fn ↝ t ] x be! [ fn ↝ t ] x₁ then [ fn ↝ t ] x₂
-- [ fn ↝ t ] ⟨ x × x₁ ⟩ = ⟨ [ fn ↝ t ] x × [ fn ↝ t ] x₁ ⟩
-- [ fn ↝ t ] (fst x) = fst ([ fn ↝ t ] x)
-- [ fn ↝ t ] (snd x) = snd ([ fn ↝ t ] x)
-- [ fn ↝ t ] ⟨ x ∣ x₁ ⟩ = ⟨ [ fn ↝ t ] x ∣ [ fn ↝ t ] x₁ ⟩
-- [ fn ↝ t ] (ask x be⟨ x₁ ∣ x₂ ⟩then x₃) =
--     ask [ fn ↝ t ] x be⟨ [ fn ↝ t ] x₁ ∣ [ fn ↝ t ] x₂ ⟩then [ fn ↝ t ] x₃
-- [ fn ↝ t ] (inl x) = inl ([ fn ↝ t ] x)
-- [ fn ↝ t ] (inr x) = inr ([ fn ↝ t ] x)
-- [ fn ↝ t ] (match x of x₁ ⇒ x₂ or x₃ ⇒ x₄) =
--     match [ fn ↝ t ] x of
--         [ fn ↝ t ] x₁ ⇒ [ fn ↝ t ] x₂ or
--         [ fn ↝ t ] x₃ ⇒ [ fn ↝ t ] x₄





-- .
