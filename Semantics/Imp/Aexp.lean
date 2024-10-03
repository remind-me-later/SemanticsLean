import Semantics.Imp.Lang

namespace Aexp
namespace Natural

inductive step: Aexp → State → Int → Prop
  | valₙ: step (val₁ n) _ n
  | varₙ: step (var₁ x) s (s x)
  | addₙ (ha: step a s n) (hb: step b s m):
    step (a + b) s (n + m)
  | subₙ (ha: step a s n) (hb: step b s m):
    step (a - b) s (n - m)
  | mulₙ (ha: step a s n) (hb: step b s m):
    step (a * b) s (n * m)

notation s " ⊢ " a " ⟹ " v => step a s v

end Natural

def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val₁ a => a
  | var₁ a => s a
  | add₁ a b => reduce a s + reduce b s
  | sub₁ a b => reduce a s - reduce b s
  | mul₁ a b => reduce a s * reduce b s

infix:100 "⇓" => reduce

-- relational definition is equal to recursive
theorem reduce.from_natural (h: s ⊢ a ⟹ n): a⇓s = n :=
  by induction h with
  | addₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | subₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | mulₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | _ => rfl

theorem Natural.from_reduce {a: Aexp} (h: a⇓s = n): s ⊢ a ⟹ n :=
  by induction a generalizing n with
  | val₁ a => exact h ▸ step.valₙ
  | var₁ a => exact h ▸ step.varₙ
  | add₁ a b iha ihb => exact h ▸ step.addₙ (iha rfl) (ihb rfl)
  | sub₁ a b iha ihb => exact h ▸ step.subₙ (iha rfl) (ihb rfl)
  | mul₁ a b iha ihb => exact h ▸ step.mulₙ (iha rfl) (ihb rfl)

theorem step_eq_reduce: (s ⊢ a ⟹ n) = (a⇓s = n) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

theorem step_eq_reduce': s ⊢ a ⟹ (a⇓s) :=
  Natural.from_reduce rfl

protected instance step.equiv: Setoid Aexp where
  r a b := ∀s n, (s ⊢ a ⟹ n) = (s ⊢ b ⟹ n)
  iseqv := {
    refl := λ _ _ _ => rfl
    symm := λ h s n => (h s n).symm
    trans := λ h1 h2 s n => (h1 s n) ▸ (h2 s n)
  }

instance reduce.equiv: Setoid Aexp where
  r a b := ∀s, a⇓s = b⇓s
  iseqv := {
    refl := λ _ _ => rfl
    symm := λ h s => (h s).symm
    trans := λ h1 h2 s => (h1 s) ▸ (h2 s)
  }

protected theorem step_eq_eq_reduce_eq:
  step.equiv.r a b ↔ reduce.equiv.r a b := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize h s (b⇓s)
    rw [step_eq_reduce, step_eq_reduce, eq_self, iff_true] at h
    exact h
  . intro h s _
    rw [step_eq_reduce, step_eq_reduce]
    specialize h s
    rw [h]

end Aexp
