module Term where
-- .
open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.Fin.Properties renaming (_≟_ to _≟Fin_)
open import Data.Vec
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.Product hiding (map)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)
-- .
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
-- .

-- .

-- .
FName : Set
FName = String
-- .
data Expr : Set
data Func : ℕ → Set
-- .
data Ctr : ℕ → Set where
   true : Ctr 0
   false : Ctr 0
   _▵_ : Ctr 2
-- .


data Term : Set where
   var : FName → Term
   _▵_ : Term → Term → Term
   --  c₀ : Ctr 0 → Term
   --  cₙ : ∀ {n} → Ctr n → Vec Term n → Term
-- .
data FTerm : Set where
   f-app : ∀ n → Func n → Vec Term n → FTerm
   f-term : Term → FTerm
-- .
data Pattern : ℕ → Set where
   mat : FName → Pattern 1
   _▵_ : ∀ {m n} → Pattern m → Pattern n → Pattern (m + n)
   --  c₀ : Ctr 0 → Pattern 0
   --  cₙ : ∀ {n} → Ctr n → Vec (Pattern 1) n → Pattern 0
-- .
data Case : Set where
   case : ∀ {n} → Pattern n → Expr → Case
-- .
data Func where
   fun : ∀ n → Vec FName n → Expr → Func n
-- .
data Expr where
   make_be_⇒_  : ∀ {n} → Pattern n → FTerm → Expr → Expr
   make_be!_⇒_ : ∀ {n} → Pattern n → Term → Expr → Expr
   match_of_  : ∀ {n} → Term → Vec Case n → Expr
   match?_of_ : ∀ {n} → Term → Vec Case n → Expr
-- .
-- .











-- .
