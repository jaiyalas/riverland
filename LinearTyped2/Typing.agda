module Typing where
-- .
open import Data.Product using (∃; _,_; proj₁)
-- open import Data.Product hiding (map)
-- open import Data.Bool using (not)
-- open import Data.String using (_==_)
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

data _,_⊢_∶_ : Ctx → Ctx → Expr 0 → LType → Set where
    litℕ : ∀ {n Γ Δ} → Γ , Δ  ⊢ num n ∶ Num
    -- -----------------------
    -- var : ∀ {x A Γ Δ}
    --     → DualDom (Γ , Δ)
    --     → (x , A) ∈ Γ
    --     → Γ , Δ ⊢ fv x ∶ A
    -- var! : ∀ {x A Γ Δ}
    --     → DualDom (Γ , Δ)
    --     → (x , A) ∈ Δ
    --     → Γ , Δ ⊢ fv x ∶ A
    -- .
    var : ∀ {x A Γ}
        → DomDist Γ
        → (x , A) ∈ Γ
        → Γ , [] ⊢ fv x ∶ A
    var! : ∀ {x A Δ}
        → DomDist Δ
        → (x , A) ∈ Δ
        → [] , Δ ⊢ fv x ∶ A
    -- --------------
    -- ## ‼ rules ##
    -- --------------
    ‼-I : ∀ {Δ t A}
        → [] , Δ ⊢ t ∶ A
        → [] , Δ ⊢ ! t ∶ ‼ A
    ‼-E : ∀ L {Γ Δ Γ+ Δ+ t u A B}
        → Γ , Δ ⊢ t ∶ ‼ A
        → (∀ x → x ∉ L → Γ+ , (x , A) ∷ Δ+ ⊢ (bv-opening u (fv x)) ∶ B)
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ ask t be!then u ∶ B
    -- ‼-E-restrict restricts the fv x out of (fvars u) precisely
    ‼-E-restrict : ∀ {Γ Δ Γ+ Δ+ t u A B}
        → Γ , Δ ⊢ t ∶ ‼ A
        -- if a term `G , D ⊢ t ∶ τ` can be formed
        -- then  we have `map proj₁ (G ++ D) ≡ fvars t`
        → (∀ x → x ∉ (fvars u) → Γ+ , (x , A) ∷ Δ+ ⊢ bv-opening u (fv x) ∶ B)
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ ask t be!then u ∶ B
    -- -------------
    -- ## ⊸ rules ##
    -- -------------
    ⊸-I : ∀ L {Γ Δ t A B}
        → (∀ x → x ∉ L → ((x , A) ∷ Γ) , Δ ⊢ (bv-opening t (fv x)) ∶ B)
        → Γ , Δ ⊢ ƛ t ∶ (A ⊸ B)
    ⊸-I-restrict : ∀ {Γ Δ t A B}
        → (∀ x → x ∉ (fvars t) → ((x , A) ∷ Γ) , Δ ⊢ (bv-opening t (fv x)) ∶ B)
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
    ⊗-E-restrict : ∀ {Γ Δ Γ+ Δ+ t u A B C}
        → Γ , Δ ⊢ t ∶ (A ⊗ B)
        → (∀ x y → x ∉ fvars u → y ∉ x ∷ (fvars u)
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
    ⊕-E-restrict : ∀ {Γ Δ Γ+ Δ+ t f g A B C}
        → Γ , Δ ⊢ t ∶ (A ⊕ B)
        → (∀ x → x ∉ fvars f → ((x , A) ∷ Γ+) , Δ+ ⊢ bv-opening f (fv x) ∶ C)
        → (∀ y → y ∉ fvars g → ((y , B) ∷ Γ+) , Δ+ ⊢ bv-opening g (fv y) ∶ C)
        → (Γ ++ Γ+) , (Δ ++ Δ+) ⊢ match t of f or g ∶ C


-- .
