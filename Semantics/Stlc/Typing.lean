import Semantics.Stlc.Rewrite
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
    HasTy Γ Term.tt Ty.Bool
  | false:
    HasTy Γ Term.ff Ty.Bool
  | cond (h₁: HasTy Γ b Ty.Bool) (h₂: HasTy Γ t₁ T₁) (h₃: HasTy Γ t₂ T₁):
    HasTy Γ (Term.cond b t₁ t₂) T₁

notation Γ " ⊢ " t " : " T => HasTy Γ t T

theorem typing_example_1:
  empty_ctx ⊢ ⦃λx:Bool↦x⦄ : ⦃Bool → Bool⦄ := HasTy.abs (HasTy.var rfl)

/-
## Canonical forms
-/

theorem canonical_form_bool
  (h₁: empty_ctx ⊢ t : Ty.Bool) (h₂: value t):
  (t = Term.tt) ∨ (t = Term.ff) :=
  by cases h₁ <;> cases h₂ <;> simp

theorem canonical_form_fun
  (h₁: empty_ctx ⊢ t : (Ty.Arrow T₁ T₂)) (h₂: value t):
  ∃x u, t = (Term.abs x T₁ u) :=
  by cases h₁ <;> cases h₂; simp

/-
## Progress
-/

theorem progress (h: empty_ctx ⊢ t : T):
  value t ∨ ∃t', t ⇒ t' := by
  {
    generalize he: empty_ctx = Γ at h
    induction h <;> cases he
    . rename_i h; cases h
    . exact Or.inl rfl
    . simp at *
      rename_i t₁ _ _ t₂ h₁ h₂ ih₁ ih₂
      apply Or.inr
      cases ih₁ with
      | inl h =>
        cases ih₂ with
        | inl hh =>
          have hc := canonical_form_fun h₁ h
          cases hc with
          | intro x hc =>
            cases hc with
            | intro w hc =>
              rw [hc]
              exists [x≔t₂]w
              exact step.appabs hh
        | inr h => {
          sorry
        }
      | inr h =>
        cases h with
        | intro w h =>
          exists (Term.app w t₂)
          apply step.app₁ h

  }
