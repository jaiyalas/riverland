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
open import Relation.Binary.PropositionalEquality
-- .
open import Types
open import Expr
open import FVar
open import Ctx
open import Substitution
open import Auxiliaries
-- .



--  反正 Δ 可以作弊
-- 那就盡量作弊!! replace every Δi in a case with the very same Δ
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
        → Γ , Δ ⊢ t ∶ A
        → freeCtx (dom Γ) (fvars t)
        → Γ , Δ ⊢ bang t ∶ (‼ A)
    ‼-E : ∀ L {Γ1 Δ1 Γ2 Δ2 t u A B}
        → Γ1 , Δ1 ⊢ t ∶ (‼ A)
        → (∀ x → x ∉ L → Γ2 , (x , A) ∷ Δ2 ⊢ (bv-opening u (fv x)) ∶ B)
        → (Γ1 ++ Γ2) , (Δ1 ++ Δ2) ⊢ ask t be!then u ∶ B
    -- -------------
    -- ## ⊸ rules ##
    -- -------------
    ⊸-I : ∀ L {Γ Δ t A B}
        → (∀ x → x ∉ L → ((x , A) ∷ Γ) , Δ ⊢ (bv-opening t (fv x)) ∶ B)
        → Γ , Δ ⊢ ƛ t ∶ (A ⊸ B)
    -- .
    ⊸-E : ∀ {Γ1 Δ1 Γ2 Δ2 Γ3 Δ3 A B t u}
        → Γ1 , Δ1 ⊢ t ∶ (A ⊸ B)
        → Γ2 , Δ2 ⊢ u ∶ A
        → Γ1 ⊹ Γ2 ≡ Γ3
        → Δ1 ⊹ Δ2 ≡ Δ3
        → Γ3 , Δ3 ⊢ t · u ∶ B
    -- -- -------------
    -- -- ## ⊗ rules ##
    -- -- -------------
    ⊗-I : ∀ {Γ1 Δ1 Γ2 Δ2 t u A B}
        → Γ1 , Δ1 ⊢ t ∶ A
        → Γ2 , Δ2 ⊢ u ∶ B
        → (Γ1 ++ Γ2) , (Δ1 ++ Δ2) ⊢ ⟨ t × u ⟩ ∶ (A ⊗ B)
    ⊗-E : ∀ L {Γ1 Δ1 Γ2 Δ2 t u A B C}
        → Γ1 , Δ1 ⊢ t ∶ (A ⊗ B)
        → (∀ x y → x ∉ L → y ∉ x ∷ L -- y ∉ L
            → ((y , B) ∷ ((x , A) ∷ Γ2)) , Δ2 ⊢ bv-opening (bv-opening u (fv x)) (fv y) ∶ C)
        → (Γ1 ++ Γ2) , (Δ1 ++ Δ2) ⊢ ask t be⟨×⟩then u ∶ C
    -- -- -------------
    -- -- ## ⊕ rules ##
    -- -- -------------
    ⊕-I₁ : ∀ {Γ Δ t A B}
        → Γ , Δ ⊢ t ∶ A
        → Γ , Δ ⊢ inl t ∶ (A ⊕ B)
    ⊕-I₂ : ∀ {Γ Δ u A B}
        → Γ , Δ ⊢ u ∶ B
        → Γ , Δ ⊢ inr u ∶ (A ⊕ B)
    ⊕-E : ∀ L {Γ1 Δ1 Γ2 Δ2 t f g A B C}
        → Γ1 , Δ1 ⊢ t ∶ (A ⊕ B)
        → (∀ x → x ∉ L → ((x , A) ∷ Γ2) , Δ2 ⊢ bv-opening f (fv x) ∶ C)
        → (∀ y → y ∉ L → ((y , B) ∷ Γ2) , Δ2 ⊢ bv-opening g (fv y) ∶ C)
        → (Γ1 ++ Γ2) , (Δ1 ++ Δ2) ⊢ match t of f or g ∶ C
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
-- .
