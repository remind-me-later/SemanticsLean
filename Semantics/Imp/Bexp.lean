import Semantics.Imp.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
private inductive big_step: Bexp × State → Bool → Prop
  | trueₙ: big_step (true₁, _) true
  | falseₙ: big_step (false₁, _) false
  | notₙ (h: big_step (b, s) n):
    big_step (~~~b, s) (!n)
  | andₙ (h₁: big_step (b₁, s) n₁) (h₂: big_step (b₂, s) n₂):
    big_step (b₁ &&& b₂, s) (n₁ && n₂)
  | orₙ (h₁: big_step (b₁, s) n₁) (h₂: big_step (b₂, s) n₂):
    big_step (b₁ ||| b₂, s) (n₁ || n₂)
  | eqₙ: big_step (eq₁ a₁ a₂, s) (a₁ s == a₂ s)
  | leₙ: big_step (le₁ a₁ a₂, s) (a₁ s <= a₂ s)

infix:10 " ==>ₗ " => big_step

private instance big_step.equiv: Setoid Bexp where
  r b₁ b₂ := ∀{s n}, ((b₁, s) ==>ₗ n) = ((b₂, s) ==>ₗ n)
  iseqv := {
    refl := λ _ ↦ rfl
    symm := λ h ↦ h.symm
    trans := λ h₁ h₂ ↦ h₁ ▸ h₂
  }

end Natural

-- Denotational semantics of Bexp
def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | true₁  => true
  | false₁ => false
  | not₁ b => !b.reduce s
  | and₁ b₁ b₂ => b₁.reduce s && b₂.reduce s
  | or₁ b₁ b₂  => b₁.reduce s || b₂.reduce s
  | eq₁ a₁ a₂  => a₁ s == a₂ s
  | le₁ a₁ a₂  => a₁ s <= a₂ s

instance: CoeFun Bexp (λ _ ↦ State → Bool) := ⟨reduce⟩

instance reduce.equiv: Setoid Bexp where
  r b₁ b₂:= ∀{s}, b₁ s = b₂ s
  iseqv := {
    refl := λ _ ↦ rfl
    symm := λ h ↦ h.symm
    trans := λ h₁ h₂ ↦ h₁ ▸ h₂
  }

section Equivalence

-- relational definition is equivalent to recursive
private theorem reduce.from_natural
  (hbig_step: conf ==>ₗ x): conf.1 conf.2 = x :=
  by induction hbig_step with
  | notₙ _ ih => exact ih ▸ rfl
  | andₙ _ _ ihb₁ ihb₂ | orₙ _ _ ihb₁ ihb₂ =>
    exact ihb₁ ▸ ihb₂ ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce
  (hred: b s = x): (b, s) ==>ₗ x :=
  by induction b generalizing x with
  | true₁ => exact hred ▸ big_step.trueₙ
  | false₁ => exact hred ▸ big_step.falseₙ
  | not₁ _ ih => exact hred ▸ big_step.notₙ (ih rfl)
  | and₁ _ _ ihb₁ ihb₂ =>
    exact hred ▸ big_step.andₙ (ihb₁ rfl) (ihb₂ rfl)
  | or₁ _ _ ihb₁ ihb₂ =>
    exact hred ▸ big_step.orₙ (ihb₁ rfl) (ihb₂ rfl)
  | eq₁ => exact hred ▸ big_step.eqₙ
  | le₁ => exact hred ▸ big_step.leₙ

private theorem big_step_eq_reduce:
  ((b, s) ==>ₗ x) = (b s = x) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

private theorem big_step_eq_reduce':
  (b, s) ==>ₗ b s :=
  Natural.from_reduce rfl

private theorem not_true_eq_false:
  (!(reduce b s)) = (~~~b) s :=
  rfl

private theorem big_step_eq_eq_reduce_eq:
  Natural.big_step.equiv.r b₁ b₂ ↔ reduce.equiv.r b₁ b₂ := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . exact λ h ↦ (big_step_eq_reduce ▸ h).mpr $ big_step_eq_reduce.mpr rfl
  . exact λ h ↦
    {
      mp := λ h1 ↦ (h ▸ (big_step_eq_reduce ▸ h1)) ▸ big_step_eq_reduce',
      mpr := λ h1 ↦ (h ▸ (big_step_eq_reduce ▸ h1)) ▸ big_step_eq_reduce'
    }

end Equivalence

end Bexp
