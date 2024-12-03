import Semantics.Imp.Lang

namespace Aexp
namespace Natural

private inductive big_step: Aexp × State → Int → Prop
  | valₙ: big_step (val₁ n, _) n
  | varₙ: big_step (var₁ v, s) (s v)
  | addₙ (ha₁: big_step (a₁, s) n₁) (ha₂: big_step (a₂, s) n₂):
    big_step (a₁ + a₂, s) (n₁ + n₂)
  | subₙ (ha₁: big_step (a₁, s) n₁) (ha₂: big_step (a₂, s) n₂):
    big_step (a₁ - a₂, s) (n₁ - n₂)
  | mulₙ (ha₁: big_step (a₁, s) n₁) (ha₂: big_step (a₂, s) n₂):
    big_step (a₁ * a₂, s) (n₁ * n₂)

infix:10 " ==>ₐ " => big_step

private instance big_step.equiv: Setoid Aexp where
  r a₁ a₂ := ∀{s n}, ((a₁, s) ==>ₐ n) = ((a₂, s) ==>ₐ n)
  iseqv := {
    refl := λ _ ↦ rfl
    symm := (·.symm)
    trans := (· ▸ ·)
  }

end Natural

def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val₁ n => n
  | var₁ v => s v
  | add₁ a₁ a₂ => a₁.reduce s + a₂.reduce s
  | sub₁ a₁ a₂ => a₁.reduce s - a₂.reduce s
  | mul₁ a₁ a₂ => a₁.reduce s * a₂.reduce s

instance: CoeFun Aexp (λ _ ↦ State → Int) := ⟨reduce⟩

instance reduce.equiv: Setoid Aexp where
  r a₁ a₂ := ∀{s}, a₁ s = a₂ s
  iseqv := {
    refl := λ _ ↦ rfl
    symm := λ h ↦ h.symm
    trans := λ h₁ h₂ ↦ h₁ ▸ h₂
  }

section Equivalence

-- relational definition is equal to recursive
private theorem reduce.from_natural
  (hbig_step: conf ==>ₐ n): conf.1 conf.2 = n :=
  by induction hbig_step with
  | addₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | subₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | mulₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce
  (hred: a s = n): (a, s) ==>ₐ n :=
  by induction a generalizing n with
  | val₁ a => exact hred ▸ big_step.valₙ
  | var₁ a => exact hred ▸ big_step.varₙ
  | add₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ big_step.addₙ (iha₁ rfl) (iha₂ rfl)
  | sub₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ big_step.subₙ (iha₁ rfl) (iha₂ rfl)
  | mul₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ big_step.mulₙ (iha₁ rfl) (iha₂ rfl)

private theorem big_step_eq_reduce:
  ((a, s) ==>ₐ n) = (a s = n) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

private theorem big_step_eq_reduce':
  (a, s) ==>ₐ a s :=
  Natural.from_reduce rfl

private theorem big_step_eq_eq_reduce_eq:
  Natural.big_step.equiv.r a₁ a₂ ↔ reduce.equiv.r a₁ a₂ := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize @h s (a₂ s)
    rw [big_step_eq_reduce, big_step_eq_reduce, eq_self, iff_true] at h
    exact h
  . intro h s _
    rw [big_step_eq_reduce, big_step_eq_reduce]
    specialize @h s
    rw [h]

end Equivalence

end Aexp
