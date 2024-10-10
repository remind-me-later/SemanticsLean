import Semantics.Imp.Lang

namespace Aexp
namespace Natural

private inductive step: Aexp × State → Int → Prop
  | valₙ: step (val₁ n, _) n
  | varₙ: step (var₁ v, s) (s v)
  | addₙ (ha₁: step (a₁, s) n₁) (ha₂: step (a₂, s) n₂):
    step (a₁ + a₂, s) (n₁ + n₂)
  | subₙ (ha₁: step (a₁, s) n₁) (ha₂: step (a₂, s) n₂):
    step (a₁ - a₂, s) (n₁ - n₂)
  | mulₙ (ha₁: step (a₁, s) n₁) (ha₂: step (a₂, s) n₂):
    step (a₁ * a₂, s) (n₁ * n₂)

infix:10 " ⟹ₐ " => step

private instance step.equiv: Setoid Aexp where
  r a₁ a₂ := ∀s n, ((a₁, s) ⟹ₐ n) = ((a₂, s) ⟹ₐ n)
  iseqv := {
    refl := λ _ _ _ => rfl
    symm := λ h s n => (h s n).symm
    trans := λ h₁ h₂ s n => (h₁ s n) ▸ (h₂ s n)
  }

end Natural

def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val₁ a => a
  | var₁ a => s a
  | add₁ a₁ a₂ => a₁.reduce s + a₂.reduce s
  | sub₁ a₁ a₂ => a₁.reduce s - a₂.reduce s
  | mul₁ a₁ a₂ => a₁.reduce s * a₂.reduce s

instance: CoeFun Aexp (λ _ => State → Int) := ⟨reduce⟩

instance reduce.equiv: Setoid Aexp where
  r a₁ a₂ := ∀s, a₁ s = a₂ s
  iseqv := {
    refl := λ _ _ => rfl
    symm := λ h s => (h s).symm
    trans := λ h₁ h₂ s => (h₁ s) ▸ (h₂ s)
  }

section Equivalence

-- relational definition is equal to recursive
private theorem reduce.from_natural
  (hstep: conf ⟹ₐ n): conf.1 conf.2 = n :=
  by induction hstep with
  | addₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | subₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | mulₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce
  (hred: a s = n): (a, s) ⟹ₐ n :=
  by induction a generalizing n with
  | val₁ a => exact hred ▸ step.valₙ
  | var₁ a => exact hred ▸ step.varₙ
  | add₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ step.addₙ (iha₁ rfl) (iha₂ rfl)
  | sub₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ step.subₙ (iha₁ rfl) (iha₂ rfl)
  | mul₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ step.mulₙ (iha₁ rfl) (iha₂ rfl)

private theorem step_eq_reduce:
  ((a, s) ⟹ₐ n) = (a s = n) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

private theorem step_eq_reduce':
  (a, s) ⟹ₐ a s :=
  Natural.from_reduce rfl

private theorem step_eq_eq_reduce_eq:
  Natural.step.equiv.r a₁ a₂ ↔ reduce.equiv.r a₁ a₂ := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize h s (a₂ s)
    rw [step_eq_reduce, step_eq_reduce, eq_self, iff_true] at h
    exact h
  . intro h s _
    rw [step_eq_reduce, step_eq_reduce]
    specialize h s
    rw [h]

end Equivalence

end Aexp
