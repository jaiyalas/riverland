module Typing where
-- .
open import Data.String renaming (_++_ to _++S_; _≟_ to _≟S_)
open import Data.Product using (∃; _,_; proj₁)
-- open import Data.Product hiding (map)
-- open import Data.Bool using (not)
open import Data.String using (_≟_)
open import Data.List
open import Data.List.Any as Any
open import Data.List.All as All
open Any.Membership-≡ using (_∈_; _∉_)
open import Relation.Nullary using (¬_; yes; no)
-- .
open import Types
open import Expr
open import FVar
open import Ctx
open import Substitution
-- .

postulate
    freeCtx : (Γ : FNames) → (t : FNames) → All.All (λ x → x ∉ Γ) t
-- freeCtx Γ [] = []
-- freeCtx Γ (x ∷ xs) with Any.any (λ g → x ≟S g) Γ
-- freeCtx Γ (x ∷ xs) | yes p = {! p  !}
-- freeCtx Γ (x ∷ xs) | no ¬p = (λ z → ¬p z) ∷ (freeCtx Γ xs)
-- .


data _,_⊢_∶_ : Ctx → Ctx → Expr 0 → LType → Set where
    litℕ : ∀ {n Γ Δ} → Γ , Δ  ⊢ num n ∶ Num
    -- -----------------------
    var : ∀ {x A Γ Δ}
        → DualDomDist Γ Δ
        → (x , A) ∈ Γ
        → Γ , Δ ⊢ fv x ∶ A
    var! : ∀ {x A Γ Δ}
        → DualDomDist Γ Δ
        → (x , A) ∈ Δ
        → Γ , Δ ⊢ fv x ∶ A
    -- --------------
    -- ## ‼ rules ##
    -- --------------
    -- ‼-I : ∀ {Δ t A}
    --     → [] , Δ ⊢ t ∶ A
    --     → [] , Δ ⊢ ! t ∶ (‼ A)
    ‼-I : ∀ {Γ Δ t A}
        -- → freeCtx (dom Γ) (fvars t) -- wwwwwwwwwwwwwwww
        → All.All (λ x → x ∉ (dom Γ)) (fvars t)
        → Γ , Δ ⊢ t ∶ A
        → Γ , Δ ⊢ bang t ∶ (‼ A)
    ‼-E : ∀ L {Γ Δ Γ+ Δ+ t u A B}
        → Γ , Δ ⊢ t ∶ (‼ A)
        → (∀ x → x ∉ L → Γ+ , (x , A) ∷ Δ+ ⊢ (bv-opening u (fv x)) ∶ B)
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ ask t be!then u ∶ B
    -- -------------
    -- ## ⊸ rules ##
    -- -------------
    ⊸-I : ∀ L {Γ Δ t A B}
        → (∀ x → x ∉ L → ((x , A) ∷ Γ) , Δ ⊢ (bv-opening t (fv x)) ∶ B)
        → Γ , Δ ⊢ ƛ t ∶ (A ⊸ B)
    ⊸-E : ∀ {Γ Δ Γ+ Δ+ A B t u}
        → Γ , Δ ⊢ t ∶ (A ⊸ B)
        → Γ+ , Δ+ ⊢ u ∶ A
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ t · u ∶ B
    -- -- -------------
    -- -- ## & rules ##
    -- --  (privilege)
    -- -- -------------
    &-I : ∀ {Γ Δ t u A B}
        → Γ , Δ ⊢ t ∶ A
        → Γ , Δ ⊢ u ∶ B
        → Γ , Δ ⊢ ⟨ t ∣ u ⟩ ∶ (A & B)
    &-E₁ : ∀ {Γ Δ t A B}
        → Γ , Δ ⊢ t ∶ (A & B)
        → Γ , Δ ⊢ fst t ∶ A
    &-E₂ : ∀ {Γ Δ t A B}
        → Γ , Δ ⊢ t ∶ (A & B)
        → Γ , Δ ⊢ snd t ∶ B
    -- -- -------------
    -- -- ## ⊗ rules ##
    -- -- -------------
    ⊗-I : ∀ {Γ Δ Γ+ Δ+ t u A B}
        → Γ , Δ ⊢ t ∶ A
        → Γ+ , Δ+ ⊢ u ∶ B
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ ⟨ t × u ⟩ ∶ (A ⊗ B)
    ⊗-E : ∀ L {Γ Δ Γ+ Δ+ t u A B C}
        → Γ , Δ ⊢ t ∶ (A ⊗ B)
        → (∀ x y → x ∉ L → y ∉ x ∷ L -- y ∉ L
            → ((y , B) ∷ ((x , A) ∷ Γ+)) , Δ+ ⊢ bv-opening (bv-opening u (fv x)) (fv y) ∶ C)
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ ask t be⟨×⟩then u ∶ C
    -- -- -------------
    -- -- ## ⊕ rules ##
    -- -- -------------
    ⊕-I₁ : ∀ {Γ Δ t A B}
        → Γ , Δ ⊢ t ∶ A
        → Γ , Δ ⊢ inl t ∶ (A ⊕ B)
    ⊕-I₂ : ∀ {Γ Δ u A B}
        → Γ , Δ ⊢ u ∶ B
        → Γ , Δ ⊢ inr u ∶ (A ⊕ B)
    ⊕-E : ∀ L {Γ Δ Γ+ Δ+ t f g A B C}
        → Γ , Δ ⊢ t ∶ (A ⊕ B)
        → (∀ x → x ∉ L → ((x , A) ∷ Γ+) , Δ+ ⊢ bv-opening f (fv x) ∶ C)
        → (∀ y → y ∉ L → ((y , B) ∷ Γ+) , Δ+ ⊢ bv-opening g (fv y) ∶ C)
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ match t of f or g ∶ C

-- .
