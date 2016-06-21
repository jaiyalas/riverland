module Typing where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; _,_)
open import Data.Product hiding (map)
open import Data.Bool using (not)
open import Data.String using (_==_)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)

open import Expr
open import Types
open import Substitution

-- .
-- DomDist 是用來確定 ctx 裡面沒有撞名, i.e., (x , A) ∷ (x , B) ∷ Γ
-- 好像後面證東西會用到... 好像..
-- data DomDist : Ctx → Set where
data DomDist {A : Set} : Assoc FName A → Set where
    [] : DomDist []
    _∷_ : ∀ {Γ x τ}
         → (x∉ : x ∉ (Data.List.map proj₁ Γ))
         → DomDist Γ
         → DomDist ((x , τ) ∷ Γ)
-- .

rmEle : FName → Ctx → Ctx
rmEle x = filter (λ a → not ((proj₁ a) == x))

{-
require something from [Γ]:
    + contraction
    + ⟪⟫-I (i.e. !-I )
    + ⟪⟫-E (i.e. !-E)
require something from Γ (i.e. <Γ>):
    + ⊸-I
    + ⊗-E
    + ⊕-E
-}

-- 要改成 Expr 0!!!
-- 原則上所有討論的基準點都是 Expr 0!!! 也就是 locally closed
-- 也許也可以考慮來證一下 lc 這個性質
data _,_⊢_∶_ {n : ℕ} : Ctx → Ctx → Expr n → LType → Set where
    -- ----------------------
    -- ## structural rules ##
    -- structure rules 可以定成 term 這樣
    -- 但是據說大家喜歡把這些當做 theorem 去證明
    -- 不知道個有什麼優缺點 可能要試試看才知道了
    -- ----------------------
    weakening : ∀ L {Γ [Γ] t A B}
        -- L 的範圍是 rule 上層的 judgements 的 term
        -- 其實可以不用這樣用外部給 L : FNames
        -- 也可以在後面給, 但是據說會比較難用(? 可能要試過才知道)
        → Γ , [Γ] ⊢ t ∶ B
        → ∀ x → x ∉ L → Γ , (x , A) ∷ [Γ] ⊢ t ∶ B
        -- x ∉ L => x ∉ Γ ++ [Γ]
        -- forall x 一定要長在這裡, 因為這是這個 judgement 的一部分
        -- 如果長在最上面那個的話就變成是 for some specific x
        -- (也就是說, existential types?)
    contraction : ∀ L {Γ [Γ] y z t A B}
        → (Γ , ((y , A) ∷ ((z , A) ∷ [Γ])) ⊢ t ∶ B)
        → ∀ x → x ∉ L → Γ , ((x , A) ∷ [Γ]) ⊢ [ y ↝ fv x ] ([ z ↝ fv x ] t) ∶ B
    exchange : ∀ {Γ [Γ] Δ [Δ] t A}
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ t ∶ A
        → (Δ ++ Γ) , ([Δ] ++ [Γ]) ⊢ t ∶ A
    -- -----------------------
    -- ## id/variable rules ##
    -- -----------------------
    -- DomDist 只需要在 var 這邊確保就好
    -- 因為 proof tree 展開以後這裡是 leaves
    -- 所以如果最末端有且中間每種 rules 都繼續保持這個特性
    -- 則整個 tree 裡面的 ctx 都會是乾淨的
    var : ∀ {x A}
        → ((x , A) ∷ []) , [] ⊢ fv x ∶ A
        -- [Γ]? []? contraction?
    var! : ∀ {[Γ] x A}
        → DomDist [Γ]
        → (x , A) ∈ [Γ]
        → [] , [Γ] ⊢ ! (fv x) ∶ ⟪ A ⟫
        -- [Γ]? []? contraction?
        -- 也可以用 var 那種定法
        -- 不過究竟要讓 [Γ] 是 singlton?
        -- 還是我們應該保持這樣
        -- 然後用 contraction 之類的去達到一樣的效果?
        -- 未定論, 不過文獻上倒是很乾脆的讓 var 和 var!
        -- 的 ctx 都只有剛好需要的那個東西
    -- --------------
    -- ## ⟪⟫ rules ##
    -- --------------
    ⟪⟫-I : ∀ {[Γ] t A}
        → [] , [Γ] ⊢ t ∶ A
        → [] , [Γ] ⊢ ! t ∶ ⟪ A ⟫
    -- ⟪⟫-I : ∀ {Γ [Γ] t A}
    --     → [] , [Γ] ⊢ t ∶ A
    --     → Γ , [Γ] ⊢ t ∶ A
    --     → Γ , [Γ] ⊢ ! t ∶ ⟪ A ⟫
    ⟪⟫-E : ∀ {Γ [Γ] Δ [Δ] x t u A B}
        → Γ , [Γ] ⊢ t ∶ ⟪ A ⟫
        → ((x , A) ∈ [Δ] → Δ , [Δ] ⊢ u ∶ B)
        → (Γ ++ Δ) , ([Γ] ++ rmEle x [Δ])
            ⊢ ask t be! ! (fv x) then u ∶ B
    -- -------------
    -- ## ⊸ rules ##
    -- -------------
    ⊸-I : ∀ L {Γ [Γ] x t A B}
        → (x ∉ L → ((x , A) ∷ Γ) , [Γ] ⊢ (t ₀↦ (fv x)) ∶ B)
        → Γ , [Γ] ⊢ ƛ t ∶ (A ⊸ B)
        -- → (x ∉ L → (x , A) ∈ Γ → Γ , [Γ] ⊢ t ∶ B)
        -- → (rmEle x Γ) , [Γ] ⊢ ƛ t ∶ (A ⊸ B)
        -- 用 (x , A) ∷ Γ 比較好
        -- rmEle x Γ 比較會造成使用上的困難 (因為不好控制 x 在哪)
    ⊸-E : ∀ {Γ [Γ] Δ [Δ] A B t u}
        → Γ , [Γ] ⊢ t ∶ (A ⊸ B)
        → Δ , [Δ] ⊢ u ∶ A
        -- 用 interleave, xs ⨄ ys ≅ zs (請參考筆記)
        -- 讓我們剛好可以選到正確的 Γ 和 Δ 切割
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ t · u ∶ B
    -- -------------
    -- ## & rules ##
    -- -------------
    &-I : ∀ {Γ [Γ] t u A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ u ∶ B
        → Γ , [Γ] ⊢ ⟨ t ∣ u ⟩ ∶ (A & B)
    &-E₁ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ (A & B)
        → Γ , [Γ] ⊢ fst t ∶ A
    &-E₂ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ (A & B)
        → Γ , [Γ] ⊢ snd t ∶ B
    -- -------------
    -- ## ⊗ rules ##
    -- -------------
    ⊗-I : ∀ {Γ [Γ] Δ [Δ] t u A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Δ , [Δ] ⊢ u ∶ B
        → (Γ ++ Δ) , ([Γ] ++ [Δ]) ⊢ ⟨ t × u ⟩ ∶ (A ⊗ B)
    ⊗-E : ∀ {Γ [Γ] Δ [Δ] t u A B C x y}
        → (L : FNames) → x ∉ L → y ∉ L
        → Γ , [Γ] ⊢ t ∶ (A ⊗ B)
        -- → ((x , A) ∷ ((y , B) ∷ Δ)) , [Δ] ⊢ u ∶ C
        → ((x , A) ∈ Γ → (y , B) ∈ Γ → (Δ , [Δ] ⊢ u ∶ C))
        → (Γ ++ (rmEle x (rmEle y Δ))) , ([Γ] ++ [Δ])
            ⊢ ask t be⟨ fv x × fv y ⟩then u ∶ C
            -- u : Expr 2
            -- locally nameless ⇒ bv 0 還是 bv ⊤?
            -- .
            -- 把 rmEle 那套改回 (x , A) ∷ Γ
    -- -------------
    -- ## ⊕ rules ##
    -- -------------
    ⊕-I₁ : ∀ {Γ [Γ] t A B}
        → Γ , [Γ] ⊢ t ∶ A
        → Γ , [Γ] ⊢ inl t ∶ (A ⊕ B)
    ⊕-I₂ : ∀ {Γ [Γ] u A B}
        → Γ , [Γ] ⊢ u ∶ B
        → Γ , [Γ] ⊢ inr u ∶ (A ⊕ B)
    ⊕-E : ∀ {Γ [Γ] Δ [Δ] t f g x y A B C}
        → (L : FNames)
        → Γ , [Γ] ⊢ t ∶ (A ⊕ B)
        → (x ∉ L → (x , A) ∈ Δ → Δ , [Δ] ⊢ f ∶ C)
        -- x ₀↤ f
        → (y ∉ L → (y , B) ∈ Δ → Δ , [Δ] ⊢ g ∶ C)
        → (Γ ++ (rmEle x (rmEle y Δ))) , ([Γ] ++ [Δ])
            ⊢ match t of fv x ⇒ f or fv y ⇒ g ∶ C
        -- 同理, locally nameless + rmEle + (f, g : Expr 1)

-- .
