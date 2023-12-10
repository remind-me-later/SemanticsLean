import Semantics.Imp.Untyped.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
inductive Step: Bexp → State → Bool → Prop
  | tt: Step tt _ true
  | ff: Step ff _ false
  | le: Step (le a b) s (a.reduce s ≤ b.reduce s)
  | not
    (h: Step a s n):
    Step (not a) s (!n)
  | and
    (h₁: Step a s n) (h₂: Step b s m):
    Step (and a b) s (n && m)

end Natural

-- Denotational semantics of Bexp
@[reducible, simp] def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | tt      => true
  | ff      => false
  | not b   => !reduce b s
  | and a b => reduce a s && reduce b s
  | le a b  => a.reduce s ≤ b.reduce s

-- relational definition is equivalent to recursive
theorem Natural.from_reduce {b: Bexp} (h: b.reduce s = x): Step b s x :=
  by induction b generalizing x with
  | tt => exact h ▸ Step.tt
  | ff => exact h ▸ Step.ff
  | le => exact h ▸ Step.le
  | not _ ih => exact h ▸ Step.not (ih rfl)
  | and _ _ l r => exact h ▸ Step.and (l rfl) (r rfl)

theorem reduce.from_natural (h: Natural.Step b s x): reduce b s = x :=
  by induction h with
  | not _ ih => exact ih ▸ rfl
  | and _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl
  | _ => rfl

@[simp] theorem Step_eq_reduce {b: Bexp}: Natural.Step b s r ↔ reduce b s = r := ⟨reduce.from_natural, Natural.from_reduce⟩

theorem not_true_eq_false: (!b.reduce s) = (not b).reduce s := by simp

protected instance Step.equiv: Setoid Bexp where
  r a b := ∀ s n, Natural.Step a s n = Natural.Step b s n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

@[reducible, simp]
instance reduce.equiv: Setoid Bexp where
  r a b:= ∀s, a.reduce s = b.reduce s
  iseqv := ⟨λ _ _ ↦ Eq.refl _, (Eq.symm $ · ·) , λ h₁ h₂ s ↦ (h₁ s) ▸ (h₂ s)⟩

protected theorem Step_eq_eq_reduce_eq: Step.equiv.r a b ↔ reduce.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    intro s
    specialize h s
    exact h
  . simp [Setoid.r] at *
    simp [h]

end Bexp
