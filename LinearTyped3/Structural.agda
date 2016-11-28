module Structural where
-- .
open import Data.Product using (∃; _,_; proj₁)
open import Data.Sum
-- open import Data.Product hiding (map)
-- open import Data.Bool using (not)
open import Data.String renaming (_++_ to _++S_; _≟_ to _≟S_)
open import Data.List
open import Data.List.Any as Any
open import Data.List.All as All
open Any.Membership-≡ using (_∈_; _∉_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality hiding ([_])
-- .
open import Types
open import Expr
open import FVar
open import Ctx
open import Substitution
open import Typing
open import Auxiliaries
-- .

-- .
⊢-weaken : ∀ Γ Δₗ Δᵣ x A {t T}
        → x ∉ dom (Γ ++ Δₗ ++ Δᵣ)
        → Γ , (Δₗ              ++ Δᵣ) ⊢ t ∶ T
        → Γ , (Δₗ ++ [(x , A)] ++ Δᵣ) ⊢ t ∶ T
-- .
⊢-weaken Γ Δₗ Δᵣ x A {num x₁} x∉ctx litℕ = litℕ
⊢-weaken Γ Δₗ Δᵣ x A {fv x₁} x∉ctx (var ddd x₁∈Γ) =
    var (DDD-insert Γ Δₗ Δᵣ x ddd x∉ctx) x₁∈Γ
⊢-weaken Γ Δₗ Δᵣ x A {fv x₁} x∉ctx (var! ddd x₁∈Δ) =
    var! (DDD-insert Γ Δₗ Δᵣ x ddd x∉ctx) (∈-++-weaken Δₗ ([ (x , A) ]) Δᵣ x₁∈Δ)
⊢-weaken Γ Δₗ Δᵣ x A {bv i} x∉ctx ()
⊢-weaken Γ Δₗ Δᵣ x A {ƛ t} x∉ctx (⊸-I ctx {A = A2} t[∀z/n]) =
    ⊸-I (x ∷ ctx)
        (λ y y∉x∷ctx →
            ⊢-weaken ((y , A2) ∷ Γ) Δₗ Δᵣ x A
                -- x∉y∷ctx
                (λ x∈y∷ctx → x∉ctx (∈-tail (¬≡-sym (∉→¬≡ y∉x∷ctx)) x∈y∷ctx))
                -- t[y/n] ; y∉ctx
                (t[∀z/n] y (λ y∈ctx → y∉x∷ctx (there y∈ctx))))


-- .
⊢-weaken Γ Δₗ Δᵣ x A {t · t₁} x∉ctx (⊸-E {Γ1} {Δ1} {Γ2} {Δ2} {_} {_} {ArgT} {RtT}  h1 h2 Γ1⊹Γ2≡Γ Δ1⊹Δ2≡Δₗ++Δᵣ)
    with ⊹≡-insertMiddle {_} {Δ1} {Δ2} {Δₗ} {Δᵣ} (x , A) Δ1⊹Δ2≡Δₗ++Δᵣ
-- .
... | inj₂ (xs , ys , xs++ys≡Δ2 , inΔ2) rewrite (sym xs++ys≡Δ2)
    = ⊸-E h1 (⊢-weaken Γ2 xs ys x A (pleaseKillMe {_} {_} {Γ2} {xs} {ys} x wtf)
        h2) Γ1⊹Γ2≡Γ inΔ2
            where
                postulate
                    wtf : x ∉ dom Γ2 ++ dom (xs ++ ys)
                -- wtf = ∉-++-tail (dom Γ1) (dom Γ2) (dom (xs ++ ys))
                --     (justKillMe {_} {_} {Γ} {Γ1} {Γ2} {Δₗ} {Δᵣ} {Δ1} {Δ2} {xs} {ys}
                --         x Γ1⊹Γ2≡Γ Δ1⊹Δ2≡Δₗ++Δᵣ xs++ys≡Δ2 x∉ctx)
-- .
... | inj₁ (xs , ys , xs++ys≡Δ1 , inΔ1) -- rewrite xs++ys≡Δ1
    = ⊸-E (⊢-weaken Γ1 xs ys x A (pleaseKillMe {_} {_} {Γ1} {xs} {ys} x wtf) {! h1'  !}) h2 Γ1⊹Γ2≡Γ inΔ1
        where
            h1' : Γ1 , xs ++ ys ⊢ t ∶ (ArgT ⊸ RtT)
            h1' rewrite xs++ys≡Δ1 = h1
            -- .
            wtf : x ∉ dom Γ1 ++ dom (xs ++ ys)
            wtf = ∉-++-dropMiddle (dom Γ1) (dom Γ2) (dom (xs ++ ys))
                (justKillMe' {_} {_} {Γ} {Γ1} {Γ2} {Δₗ} {Δᵣ} {Δ1} {Δ2} {xs} {ys}
                    x Γ1⊹Γ2≡Γ Δ1⊹Δ2≡Δₗ++Δᵣ xs++ys≡Δ1 x∉ctx)
-- .
-- .
            -- non-terminated
    -- The very 1st parameter of ⊸-E is filled with `h1`
    --   in which we know how the left-half-Γ is selected.
    --   Thus agda can also derive the right-half-Γ should be.
    --   This is the reason why we can use `_` in `⊢-weaken`.
    -- .
    -- The proble now is that, we need to know how to split `Δₗ++Δᵣ` into `Δ1⊹Δ2`.
    -- This could be down with applying further case analysis by using `with`.
    -- .
    -- ⊸-E h1 (⊢-weaken _ {!   !} {!   !} x A {!   !} h2) Γ1⊹Γ2≡Γ {!   !}
    -- .
    -- ################################################################
    -- .
    -- On second tought, we should be able to weaken on left or right,
    -- i.e., function body or argument.
    -- ⊸-E nh1 nh2 Γ1⊹Γ2≡Γ {! something like map (insertMiddle x) Δ1⊹Δ2≡Δₗ++Δᵣ  !}
    --     where
    --         nh1 = {!   !}
    --         nh2 = {!   !}

⊢-weaken Γ Δₗ Δᵣ x A {bang t} x∉ctx (‼-I x₁ p) =
    ‼-I (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx x₁) p
⊢-weaken Γ Δₗ Δᵣ x A {ask t be!then t₁} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {⟨ t ∣ t₁ ⟩} x∉ctx (&-I p p₁) =
    &-I (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p) (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p₁)
⊢-weaken Γ Δₗ Δᵣ x A {⟨ t × t₁ ⟩} x∉ctx p = {! p  !}
⊢-weaken Γ Δₗ Δᵣ x A {ask t be⟨×⟩then t₁} x∉ctx p = {! p   !}
⊢-weaken Γ Δₗ Δᵣ x A {inl t} x∉ctx (⊕-I₁ p) = ⊕-I₁ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
⊢-weaken Γ Δₗ Δᵣ x A {inr t} x∉ctx (⊕-I₂ p) = ⊕-I₂ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
⊢-weaken Γ Δₗ Δᵣ x A {match t of t₁ or t₂} x∉ctx p = {! p   !}
⊢-weaken Γ Δₗ Δᵣ x A {fst t} {T} x∉ctx (&-E₁ p) =
    &-E₁ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
⊢-weaken Γ Δₗ Δᵣ x A {snd t} x∉ctx (&-E₂ p) =
    &-E₂ (⊢-weaken Γ Δₗ Δᵣ x A x∉ctx p)
-- .

-- .
⊢-exchange : ∀ Γ1 Γ2 Δ1 Δ2 {t T}
    → (Γ1 ++ Γ2) , (Δ1 ++ Δ2) ⊢ t ∶ T
    → (Γ2 ++ Γ1) , (Δ2 ++ Δ1) ⊢ t ∶ T
⊢-exchange Γ1 Γ2 Δ1 Δ2 p = {! p  !}
-- .

-- .
⊢-contr : ∀ Γ Δ1 Δ2 x y z A {t T}
    → Γ , (Δ1 ++ (x , A) ∷ (y , A) ∷ Δ2) ⊢ t ∶ T
    → Γ , (Δ1 ++ (z , A) ∷ Δ2) ⊢ [ y ↝ fv z ] ([ x ↝ fv z ] t) ∶ T
⊢-contr Γ Δ1 Δ2 x y z A p = {! p  !}

-- .
