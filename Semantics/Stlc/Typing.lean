import Semantics.Stlc.Natural
import Mathlib.Logic.Function.Basic

def Context := String → Option Ty
def empty_ctx: Context := λ _ ↦ none

inductive HasTy: Context → Term → Ty → Prop where
  | var (h: Γ x = some T):
    HasTy Γ (Term.var x) T
  | abs (h: HasTy (Function.update Γ x (some T₂)) t T₁):
    HasTy Γ (Term.abs x T₂ t) (Ty.Arrow T₂ T₁)
  | app (h₁: HasTy Γ t₁ (Ty.Arrow T₂ T₁)) (h₂: HasTy Γ t₂ T₂):
    HasTy Γ (Term.app t₁ t₂) T₁
  | true:
    HasTy Γ (Term.true) Ty.Bool
  | false:
    HasTy Γ (Term.false) Ty.Bool
  | cond (h₁: HasTy Γ b Ty.Bool) (h₂: HasTy Γ t₁ T₁) (h₃: HasTy Γ t₂ T₁):
    HasTy Γ (Term.cond b t₁ t₂) T₁

notation Γ " ⊢ " t " : " T => HasTy Γ t T

theorem typing_example_1:
  empty_ctx ⊢ ⦃λx:Bool↦x⦄ : ⦃Bool → Bool⦄ := HasTy.abs (HasTy.var rfl)

/-
## Canonical forms
-/

theorem canonical_form_bool
  (h₁: empty_ctx ⊢ t : Ty.Bool) (h₂: Term.Value t):
  (t = Term.true) ∨ (t = Term.false) :=
  by cases h₁ <;> cases h₂ <;> simp

theorem canonical_form_fun
  (h₁: empty_ctx ⊢ t : (Ty.Arrow T₁ T₂)) (h₂: Term.Value t):
  ∃x u, t = (Term.abs x T₁ u) :=
  by cases h₁ <;> cases h₂; simp
