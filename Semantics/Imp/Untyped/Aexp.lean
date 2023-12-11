import Semantics.Imp.Untyped.Lang

namespace Aexp
namespace Natural

inductive Step: Aexp → State → Val → Prop
  | val: Step (val n) _ n
  | var: Step (var x) s (s x)
  | add
    (h₁: Step a s n) (h₂: Step b s m):
    Step (add a b) s (n + m)

end Natural

@[reducible]
def reduce (a: Aexp) (s: State): Val :=
  match a with
  | val n => n
  | var x => s x
  | add a b => reduce a s + reduce b s

-- relational definition is equal to recursive
theorem reduce.from_natural (h: Natural.Step a s n): reduce a s = n :=
  by induction h with
  | add _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl
  | _ => rfl

theorem Natural.from_reduce {a: Aexp} (h: reduce a s = n): Step a s n :=
  by induction a generalizing n with
  | val _ => exact h ▸ Step.val
  | var _ => exact h ▸ Step.var
  | add _ _ l r => exact h ▸ Step.add (l rfl) (r rfl)

@[simp] theorem Step_iff_reduce: Natural.Step a s n ↔ reduce a s = n := ⟨reduce.from_natural, Natural.from_reduce⟩
@[simp] theorem Step_iff_reduce': Natural.Step a s (reduce a s) := Natural.from_reduce rfl

protected instance Step.equiv: Setoid Aexp where
  r a b := ∀ s n, Natural.Step a s n = Natural.Step b s n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

instance reduce.equiv: Setoid Aexp where
  r a b := ∀s, reduce a s = reduce b s
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
