module Types where
--
data Typ = TypAny -- ???
         | TypNat
         | TypBool
         | TypProd Typ Typ
         | TypFunc Typ Typ
         -- | TypSum Typ Typ
         deriving (Show, Eq)

class Product a where
    times :: a -> a -> a
instance Product Typ where
    times = TypProd

--
-- LetIn MTerm Expr Expr
-- DupIn MTerm VTerm Expr
-- --
-- Match VTerm [Case]
-- MatEq VTerm Case Case

-- num : ∀ {n} → ℕ → Expr n
-- fv  : ∀ {n} → (x : FName) → Expr n
-- bv  : ∀ {n} → (i : Fin n) → Expr n
-- ===================================
-- Term VTerm

-- -- ⊸-I/E
-- ƛ   : ∀ {n} → (f : Expr (suc n)) → Expr n
-- _·_ : ∀ {n} → (f : Expr n) → (e : Expr n) → Expr n
-- ===================================
-- Lambda MTerm Expr
-- AppIn MTerm FApp Expr

-- -- ⟪⟫-I/E
-- bang_  : ∀ {n} → Expr n → Expr n
-- ask_be!then_ : ∀ {n}
--     → (e : Expr n)
--     → (f : Expr (suc n))
--     → Expr n
-- ===================================

-- -- ⊗-I/E
-- ⟨_×_⟩ : ∀ {n} → (e₁ : Expr n) → (e₂ : Expr n) → Expr n
-- ask_be⟨×⟩then_ : ∀ {n}
--     → (e : Expr n)
--     → (f : Expr (suc (suc n)))
--     → Expr n
-- ===================================
-- Pair Expr Expr
-- LetIn MTerm Expr Expr

-- -- ⊕-I/E
-- inl : ∀ {n} → (e : Expr n) → Expr n
-- inr : ∀ {n} → (e : Expr n) → Expr n
-- match_of_or_ : ∀ {n}
--     → (e  : Expr n)
--     → (f : Expr (suc n))
--     → (g : Expr (suc n))
--     → Expr n
-- ===================================
-- none

-- -- &-I/E
-- ⟨_∣_⟩ : ∀ {n} → (f : Expr n) → (g : Expr n) → Expr n
-- fst   : ∀ {n} → (e : Expr n) → Expr n
-- snd   : ∀ {n} → (e : Expr n) → Expr n
-- ===================================
-- none

-- data Val     = N Nat
--              | B Bool
--              | Pr Val Val
--              | Closure Env Expr
--              deriving (Eq)
--
