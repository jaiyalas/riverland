module TypeSafety where





⊢-weaken : ∀ Γ x τ Δ {e σ}
           → x ∉ dom (Γ ++ Δ)
           → (Γ ++ Δ) ⊢ e ∶ σ
           → (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
-- .
⊢-subst : ∀ Γ x τ Δ {e t σ}
          → (Γ ++ [(x , τ)] ++ Δ) ⊢ e ∶ σ
          → (Γ ++ Δ) ⊢ t ∶ τ
          → (Γ ++ Δ) ⊢ [ x ↝ t ] e ∶ σ
-- .
preservation : ∀ {e e' : Expr} {τ}
               → [] ⊢ e ∶ τ
               → e ⟼ e'
               → [] ⊢ e' ∶ τ
-- .
progress : ∀ {e : Expr} {τ}
           → [] ⊢ e ∶ τ
           → ¬ (Val e)
           → ∃ (λ e' → e ⟼ e')
-- .
