import Semantics.Imp.Untyped.Syntax
import Semantics.Relation

namespace Aexp
namespace Natural

-- Operational semantics of aexp
inductive Step: Aexp × State → Val → Prop
  | val₁:
    Step (val n, _) n

  | loc₁:
    Step (loc x, s) (s x)

  | add₁ (h₁: Step (a, s) n) (h₂: Step (b, s) m):
    Step (add a b, s) (n + m)

  | sub₁ (h₁: Step (a, s) n) (h₂: Step (b, s) m):
    Step (sub a b, s) (n - m)

  | mul₁ (h₁: Step (a, s) n) (h₂: Step (b, s) m):
    Step (mul a b, s) (n * m)

infix:110 " ⟹ " => Step

theorem reducing: reducing Step := by {
  unfold reducing
  intro t
  cases t with | mk f s => {
    induction f with
    | val n => exact ⟨n, Step.val₁⟩
    | loc x => exact ⟨s x, Step.loc₁⟩
    | add a b ih₁ ih₂ =>
      cases ih₁ with | intro w₁ ih₁ =>
        cases ih₂ with | intro w₂ ih₂ =>
          exact ⟨w₁ + w₂, Step.add₁ ih₁ ih₂⟩
    | sub a b ih₁ ih₂ =>
      cases ih₁ with | intro w₁ ih₁ =>
        cases ih₂ with | intro w₂ ih₂ =>
          exact ⟨w₁ - w₂, Step.sub₁ ih₁ ih₂⟩
    | mul a b ih₁ ih₂ =>
      cases ih₁ with | intro w₁ ih₁ =>
        cases ih₂ with | intro w₂ ih₂ =>
          exact ⟨w₁ * w₂, Step.mul₁ ih₁ ih₂⟩
  }
}

theorem determinist: determinist Step := by {
  unfold determinist
  intro a b c h₁ h₂
  induction h₁ generalizing c with
  | val₁ => cases h₂; rfl
  | loc₁ => cases h₂; rfl
  | add₁ _ _ ih₁ ih₂ =>
    cases h₂ with | add₁ h₁ h₂ =>
      exact (ih₁ _ h₁) ▸ (ih₂ _ h₂) ▸ rfl
  | sub₁ _ _ ih₁ ih₂ =>
    cases h₂ with | sub₁ h₁ h₂ =>
      exact (ih₁ _ h₁) ▸ (ih₂ _ h₂) ▸ rfl
  | mul₁ _ _ ih₁ ih₂ =>
    cases h₂ with | mul₁ h₁ h₂ =>
      exact (ih₁ _ h₁) ▸ (ih₂ _ h₂) ▸ rfl
}

end Natural

-- Denotational semantics of arithmetic expressions
@[reducible]
def reduce (a: Aexp) (s: State): Val :=
  match a with
  | val n => n
  | loc x => s x
  | add a b => reduce a s + reduce b s
  | sub a b => reduce a s - reduce b s
  | mul a b => reduce a s * reduce b s

infix:110 "⇓" => reduce

-- relational definition is equal to recursive
theorem reduce.from_natural (h: as ⟹ n): reduce.uncurry as = n :=
  by induction h with
  | val₁ => rfl
  | loc₁ => rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

theorem Natural.from_reduce {a: Aexp} (h: a⇓s = n): (a,s) ⟹ n :=
  by induction a generalizing n with
  | val _ => exact h ▸ Step.val₁
  | loc _ => exact h ▸ Step.loc₁
  | add _ _ l r => exact h ▸ Step.add₁ (l rfl) (r rfl)
  | sub _ _ l r => exact h ▸ Step.sub₁ (l rfl) (r rfl)
  | mul _ _ l r => exact h ▸ Step.mul₁ (l rfl) (r rfl)

@[simp] theorem Step_iff_reduce: (a, s) ⟹ n ↔ a⇓s = n := ⟨reduce.from_natural, Natural.from_reduce⟩
@[simp] theorem Step_iff_reduce': (a, s) ⟹ (a⇓s) := Natural.from_reduce rfl

protected instance Step.equiv: Setoid Aexp where
  r a b := ∀ s n, (a, s) ⟹ n = (b, s) ⟹ n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

instance reduce.equiv: Setoid Aexp where
  r a b := ∀s, a⇓s = b⇓s
  iseqv := ⟨λ _ _ ↦ Eq.refl _, (Eq.symm $ · ·) , λ h₁ h₂ s ↦ (h₁ s) ▸ (h₂ s)⟩

protected theorem Step_eq_eq_reduce_eq: Step.equiv.r a b ↔ reduce.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    intro s
    specialize h s
    exact h
  . simp [Setoid.r] at *
    simp [h]

end Aexp
