import Semantics.Imp.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
private inductive step: Bexp × State → Bool → Prop
  | trueₙ: step (true₁, _) true
  | falseₙ: step (false₁, _) false
  | notₙ (h: step (a, s) n):
    step (~~~a, s) (!n)
  | andₙ (h₁: step (a, s) n) (h₂: step (b, s) m):
    step (a &&& b, s) (n && m)
  | orₙ (h₁: step (a, s) n) (h₂: step (b, s) m):
    step (a ||| b, s) (n || m)
  | eqₙ: step (eq₁ a b, s) (a s == b s)
  | leₙ: step (le₁ a b, s) (a s <= b s)

infix:10 " ⟹ₗ " => step

private instance step.equiv: Setoid Bexp where
  r a b := ∀s n, ((a, s) ⟹ₗ n) = ((b, s) ⟹ₗ n)
  iseqv := {
    refl := λ _ _ _ => rfl
    symm := λ h s n => (h s n).symm
    trans := λ h1 h2 s n => (h1 s n) ▸ (h2 s n)
  }

end Natural

-- Denotational semantics of Bexp
def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | true₁    => true
  | false₁   => false
  | not₁ b   => !reduce b s
  | and₁ a b => reduce a s && reduce b s
  | or₁ a b  => reduce a s || reduce b s
  | eq₁ a b  => a.reduce s == b.reduce s
  | le₁ a b  => a.reduce s <= b.reduce s

instance: CoeFun Bexp (λ _ => State → Bool) where
  coe b := reduce b

instance reduce.equiv: Setoid Bexp where
  r a b:= ∀s, a s = b s
  iseqv := {
    refl := λ _ _ => rfl
    symm := λ h s => (h s).symm
    trans := λ h1 h2 s => (h1 s) ▸ (h2 s)
  }

section Equivalence

-- relational definition is equivalent to recursive
private theorem reduce.from_natural {p: Bexp × State}
  (h: p ⟹ₗ x): p.1 p.2 = x :=
  by induction h with
  | notₙ _ ih => exact ih ▸ rfl
  | andₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | orₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce {b: Bexp}
  (h: b s = x): (b, s) ⟹ₗ x :=
  by induction b generalizing x with
  | true₁ => exact h ▸ step.trueₙ
  | false₁ => exact h ▸ step.falseₙ
  | not₁ a ih => exact h ▸ step.notₙ (ih rfl)
  | and₁ a b iha ihb => exact h ▸ step.andₙ (iha rfl) (ihb rfl)
  | or₁ a b iha ihb => exact h ▸ step.orₙ (iha rfl) (ihb rfl)
  | eq₁ => exact h ▸ step.eqₙ
  | le₁ => exact h ▸ step.leₙ

private theorem step_eq_reduce {b: Bexp}:
  ((b, s) ⟹ₗ x) = (b s = x) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

private theorem step_eq_reduce' {b: Bexp}: (b, s) ⟹ₗ b s :=
  Natural.from_reduce rfl

private theorem not_true_eq_false:
  (!(reduce b s)) = (~~~b) s :=
  rfl

private theorem step_eq_eq_reduce_eq:
  Natural.step.equiv.r a b ↔ reduce.equiv.r a b := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    exact (step_eq_reduce ▸ h s (b s)).mpr $ step_eq_reduce.mpr rfl
  . intro h s _
    constructor
    . intro h1
      exact ((h s) ▸ (step_eq_reduce ▸ h1)) ▸ step_eq_reduce'
    . intro h1
      exact ((h s) ▸ (step_eq_reduce ▸ h1)) ▸ step_eq_reduce'

end Equivalence

end Bexp
