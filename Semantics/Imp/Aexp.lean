import Semantics.Imp.Lang

namespace Aexp
namespace Natural

private inductive step: Aexp × State → Int → Prop
  | valₙ: step (val₁ n, _) n
  | varₙ: step (var₁ x, s) (s x)
  | addₙ (ha: step (a, s) n) (hb: step (b, s) m):
    step (a + b, s) (n + m)
  | subₙ (ha: step (a, s) n) (hb: step (b, s) m):
    step (a - b, s) (n - m)
  | mulₙ (ha: step (a, s) n) (hb: step (b, s) m):
    step (a * b, s) (n * m)

infix:10 " ⟹ₐ " => step

private instance step.equiv: Setoid Aexp where
  r a b := ∀s n, ((a, s) ⟹ₐ n) = ((b, s) ⟹ₐ n)
  iseqv := {
    refl := λ _ _ _ => rfl
    symm := λ h s n => (h s n).symm
    trans := λ h1 h2 s n => (h1 s n) ▸ (h2 s n)
  }

end Natural

def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val₁ a => a
  | var₁ a => s a
  | add₁ a b => reduce a s + reduce b s
  | sub₁ a b => reduce a s - reduce b s
  | mul₁ a b => reduce a s * reduce b s

instance: CoeFun Aexp (λ _ => State → Int) where
  coe a := reduce a

instance reduce.equiv: Setoid Aexp where
  r a b := ∀s, a s = b s
  iseqv := {
    refl := λ _ _ => rfl
    symm := λ h s => (h s).symm
    trans := λ h1 h2 s => (h1 s) ▸ (h2 s)
  }

section Equivalence

-- relational definition is equal to recursive
private theorem reduce.from_natural
  (h: p ⟹ₐ n): p.1 p.2 = n :=
  by induction h with
  | addₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | subₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | mulₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce {a: Aexp}
  (h: a s = n): (a, s) ⟹ₐ n :=
  by induction a generalizing n with
  | val₁ a => exact h ▸ step.valₙ
  | var₁ a => exact h ▸ step.varₙ
  | add₁ a b iha ihb => exact h ▸ step.addₙ (iha rfl) (ihb rfl)
  | sub₁ a b iha ihb => exact h ▸ step.subₙ (iha rfl) (ihb rfl)
  | mul₁ a b iha ihb => exact h ▸ step.mulₙ (iha rfl) (ihb rfl)

private theorem step_eq_reduce:
  ((a, s) ⟹ₐ n) = (a s = n) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

private theorem step_eq_reduce':
  (a, s) ⟹ₐ a s :=
  Natural.from_reduce rfl

private theorem step_eq_eq_reduce_eq:
  Natural.step.equiv.r a b ↔ reduce.equiv.r a b := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize h s $ b s
    rw [step_eq_reduce, step_eq_reduce, eq_self, iff_true] at h
    exact h
  . intro h s _
    rw [step_eq_reduce, step_eq_reduce]
    specialize h s
    rw [h]

end Equivalence

end Aexp
