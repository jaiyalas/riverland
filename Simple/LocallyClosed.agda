module LocallyClosed where

open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Fin hiding (_+_; inject)
open import Data.String hiding (_++_) renaming (_≟_ to _≟S_)
open import Data.List
open import Data.List.Any as Any
open Any.Membership-≡ using (_∈_; _∉_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_; proj₁; proj₂)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Expr
open import Substitution

data LC : ∀ {n} → Expr n → Set where
   numᶜ : ∀ {n} → (i : ℕ) → LC {n} (num i)
   fvᶜ  : ∀ {n}
       → (x : FName)
       → LC {n} (fv x)
   _·ᶜ_ : ∀ {n} {f x}
       → LC {n} f
       → LC {n} x
       → LC {n} (f · x)
   ƛᶜ   : ∀ {e}
       → (ns : FNames)
       → ( ∀ {x} → x ∉ ns → LC {0} (e ₀↦ fv x) )
       → LC {0} (ƛ e)

appᶜ₁ : ∀ {n} {f x} → LC {n} (f · x) → LC {n} f
appᶜ₁ (lcf ·ᶜ lcx) = lcf

appᶜ₂ : ∀ {n} {f x} → LC {n} (f · x) → LC {n} x
appᶜ₂ (lcf ·ᶜ lcx) = lcx

lc? : ∀ {n} → (e : Expr n) → (LC {n} e ⊎ ¬ LC {n} e)
lc? (num x) = inj₁ (numᶜ x)
lc? (bv i)  = inj₂ (λ ())
lc? (fv x)  = inj₁ (fvᶜ x)
lc? (ƛ e)   with lc? e
lc? (ƛ e) | inj₁ x = inj₁ {!   !}
lc? (ƛ e) | inj₂ y = inj₂ (λ lce → {!   !})
lc? (f · x) with lc? f | lc? x
lc? (f · x) | inj₁ f' | inj₁ x' = inj₁ (f' ·ᶜ x')
lc? (f · x) | inj₁ f' | inj₂ x' = inj₂ (λ p → x' (appᶜ₂ p))
lc? (f · x) | inj₂ f' | _       = inj₂ (λ p → f' (appᶜ₁ p))
