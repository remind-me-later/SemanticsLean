import Semantics.Imp.Lang

namespace Aexp
namespace Natural

inductive step: Aexp → State → Int → Prop
  | val: step (val n) _ n
  | var: step (var x) s (s x)
  | add (ha: step a s n) (hb: step b s m):
    step (a + b) s (n + m)
  | sub (ha: step a s n) (hb: step b s m):
    step (a - b) s (n - m)
  | mul (ha: step a s n) (hb: step b s m):
    step (a * b) s (n * m)

notation s " ⊢ " a " ⟹ " v => step a s v

end Natural

@[reducible]
def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val a => a
  | var a => s a
  | add a b => reduce a s + reduce b s
  | sub a b => reduce a s - reduce b s
  | mul a b => reduce a s * reduce b s

infix:100 "⇓" => reduce

-- relational definition is equal to recursive
theorem reduce.from_natural (h: s ⊢ a ⟹ n): a⇓s = n :=
  by induction h with
  | add _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | sub _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | mul _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | _ => rfl

theorem Natural.from_reduce {a: Aexp} (h: a⇓s = n): s ⊢ a ⟹ n :=
  by induction a generalizing n with
  | val a => exact h ▸ step.val
  | var a => exact h ▸ step.var
  | add a b iha ihb => exact h ▸ step.add (iha rfl) (ihb rfl)
  | sub a b iha ihb => exact h ▸ step.sub (iha rfl) (ihb rfl)
  | mul a b iha ihb => exact h ▸ step.mul (iha rfl) (ihb rfl)

@[simp]
theorem step_iff_reduce: (s ⊢ a ⟹ n) ↔ a⇓s = n :=
  ⟨reduce.from_natural, Natural.from_reduce⟩
@[simp]
theorem step_iff_reduce': s ⊢ a ⟹ (a⇓s) :=
  Natural.from_reduce rfl

protected instance step.equiv: Setoid Aexp where
  r a b := ∀ s n, (s ⊢ a ⟹ n) = (s ⊢ b ⟹ n)
  iseqv := {
    refl := fun _ _ _ => rfl
    symm := fun h s n => (h s n).symm
    trans := fun h1 h2 x n => (h1 x n) ▸ (h2 x n)
  }

instance reduce.equiv: Setoid Aexp where
  r a b := ∀s, a⇓s = b⇓s
  iseqv := ⟨fun _ _ => rfl, (Eq.symm $ · ·), fun h1 h2 s => (h1 s) ▸ (h2 s)⟩

protected theorem step_eq_eq_reduce_eq:
  step.equiv.r a b ↔ reduce.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    intro s
    specialize h s (b⇓s)
    rw [h]
  . simp [Setoid.r] at *
    simp [h]

end Aexp
