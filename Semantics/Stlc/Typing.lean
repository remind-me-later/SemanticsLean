import Semantics.Stlc.Rewrite
import Mathlib.Logic.Function.Basic

def Context := String → Option Ty
def Γ₀: Context := λ _ ↦ none

inductive has_type: Context → Term → Ty → Prop where
  | var (h: Γ x = some T):
    has_type Γ (Term.var x) T
  | abs (h: has_type (Function.update Γ x (some T₂)) t T₁):
    has_type Γ (Λ x:T₂ ↦ t) (T₂ → T₁)
  | app t₁ t₂
    (h₁: has_type Γ t₁ (T₂ → T₁)) (h₂: has_type Γ t₂ T₂):
    has_type Γ (t₁..t₂) T₁
  | tt:
    has_type Γ ⊤ 𝔹
  | ff:
    has_type Γ ⊥ 𝔹
  | cond t₁ t₂
    (h₁: has_type Γ b 𝔹) (h₂: has_type Γ t₁ T₁) (h₃: has_type Γ t₂ T₁):
    has_type Γ (b ? t₁ | t₂) T₁

notation Γ " ⊢ " t " : " T => has_type Γ t T

theorem typing_example_1:
  Γ₀ ⊢ ⦃Λ x:𝔹 ↦ x⦄ : ⦃𝔹 → 𝔹⦄ := has_type.abs (has_type.var rfl)

/-
## Canonical forms
-/

theorem canonical_form_bool
  (h₁: Γ₀ ⊢ t : 𝔹) (h₂: value t):
  t = ⊤ ∨ t = ⊥ :=
  by cases h₁ <;> cases h₂ <;> simp

theorem canonical_form_fun
  (h₁: Γ₀ ⊢ t : (T₁ → T₂)) (h₂: value t):
  ∃x u, t = Λ x : T₁ ↦ u :=
  by cases h₁ <;> cases h₂; simp

/-
## Progress
-/

theorem progress (h: Γ₀ ⊢ t : T): value t ∨ ∃w, t ⇒ w := by
  generalize he: Γ₀ = Γ at h
  induction h with
  | abs => exact Or.inl rfl
  | tt => exact Or.inl rfl
  | ff => exact Or.inl rfl
  | var h => cases he; cases h
  | app t₁ t₂ h₁ _ ih₁ ih₂ =>
    cases he
    simp at *
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
            exists [x ≔ t₂]w
            exact step.appabs hh
      | inr hh =>
        cases hh with
        | intro w hh =>
          exists t₁..w
          exact step.app₂ h hh
    | inr h =>
      cases h with
      | intro w h =>
        exists (Term.app w t₂)
        apply step.app₁ h
  | cond t₁ t₂ h₁ _ _ ih₁ =>
    cases he
    simp at *
    cases ih₁ with
    | inl hh =>
      apply Or.inr
      have hc := canonical_form_bool h₁ hh
      cases hc with
      | inl hc => exists t₁; rw [hc]; exact step.cond₁
      | inr hc => exists t₂; rw [hc]; exact step.cond₂
    | inr hh =>
      apply Or.inr
      cases hh with
      | intro w hh =>
        exists w ? t₁ | t₂
        exact step.cond₃ hh
