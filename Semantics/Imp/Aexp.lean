import Semantics.Imp.Lang

namespace Aexp
namespace Natural

inductive step: Aexp → State → Val → Prop
  | val: step (val n) _ n
  | var: step (var x) s (s x)
  | add
    (h₁: step a s n) (h₂: step b s m):
    step (add a b) s (n + m)

notation s " ⊢ " a " ⟹ " v => step a s v

end Natural

@[reducible]
def reduce (a: Aexp) (s: State): Val :=
  match a with
  | val n => n
  | var x => s x
  | add a b => reduce a s + reduce b s

infix:100 "⇓" => reduce

-- relational definition is equal to recursive
theorem reduce.from_natural (h: s ⊢ a ⟹ n): a⇓s = n :=
  by induction h with
  | add _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl
  | _ => rfl

theorem Natural.from_reduce {a: Aexp} (h: a⇓s = n): s ⊢ a ⟹ n :=
  by induction a generalizing n with
  | val _ => exact h ▸ step.val
  | var _ => exact h ▸ step.var
  | add _ _ l r => exact h ▸ step.add (l rfl) (r rfl)

@[simp] theorem step_iff_reduce: (s ⊢ a ⟹ n) ↔ a⇓s = n := ⟨reduce.from_natural, Natural.from_reduce⟩
@[simp] theorem step_iff_reduce': s ⊢ a ⟹ (a⇓s) := Natural.from_reduce rfl

protected instance step.equiv: Setoid Aexp where
  r a b := ∀ s n, (s ⊢ a ⟹ n) = (s ⊢ b ⟹ n)
  iseqv := {
    refl := fun _ _ _ => Eq.refl _
    symm := fun h s n => Eq.symm (h s n)
    trans := fun h₁ h₂ x n => (h₁ x n) ▸ (h₂ x n)
  }

instance reduce.equiv: Setoid Aexp where
  r a b := ∀s, a⇓s = b⇓s
  iseqv := ⟨fun _ _ => Eq.refl _, (Eq.symm $ · ·) , fun h₁ h₂ s => (h₁ s) ▸ (h₂ s)⟩

protected theorem step_eq_eq_reduce_eq: step.equiv.r a b ↔ reduce.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    intro s
    specialize h s (b⇓s)
    rw [h]
  . simp [Setoid.r] at *
    simp [h]

end Aexp
