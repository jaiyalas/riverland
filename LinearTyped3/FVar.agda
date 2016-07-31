module FVar where
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)
-- .
open import Expr
-- .
fvars : ∀ {n} → Expr n → FNames
fvars (num x) = []
fvars (fv x) = [ x ]
fvars (bv i) = []
fvars (ƛ e) = fvars e
fvars (e · e₁) = fvars e ++ fvars e₁
fvars (bang e) = fvars e
fvars (ask e be!then e₁) = fvars e ++ fvars e₁
fvars ⟨ e ∣ e₁ ⟩ = fvars e ++ fvars e₁
fvars (fst e) = fvars e
fvars (snd e) = fvars e
fvars ⟨ e × e₁ ⟩ = fvars e ++ fvars e₁
fvars (ask e be⟨×⟩then e₁) = fvars e ++ fvars e₁
fvars (inl e) = fvars e
fvars (inr e) = fvars e
fvars (match e of e₁ or e₂) = fvars e ++ fvars e₁ ++ fvars e₂
-- .
postulate
    fresh-gen      : FNames → FName
    fresh-gen-spec : ∀ ns → fresh-gen ns ∉ ns
-- .
genName : (ns : FNames) → ∃ (λ x → x ∉ ns)
genName ns = fresh-gen ns , fresh-gen-spec ns
-- .

-- .
