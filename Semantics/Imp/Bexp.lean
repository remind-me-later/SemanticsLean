import Semantics.Imp.Aexp

namespace Bexp
namespace BigStep

-- Operational semantics of Bexp
private inductive BigStep: Bexp × State → Bool → Prop
  | true: BigStep (true, _) .true
  | false: BigStep (false, _) .false
  | not (h: BigStep (b, s) x):
    BigStep (~~~b, s) !x
  | and (h1: BigStep (b, s) x) (h2: BigStep (b', s) y):
    BigStep (b &&& b', s) (x && y)
  | or (h1: BigStep (b, s) x) (h2: BigStep (b', s) y):
    BigStep (b ||| b', s) (x || y)
  | eq: BigStep (eq a a', s) (a s == a' s)
  | le: BigStep (le a a', s) (a s <= a' s)

infix:100 " ==>b " => BigStep

private instance equiv: Setoid Bexp where
  r b b' := ∀{s n}, (b, s) ==>b n ↔ (b', s) ==>b n
  iseqv := ⟨fun _ => Iff.rfl, (Iff.symm .), (Iff.trans . .)⟩

end BigStep

-- Denotational semantics of Bexp
def eval (b: Bexp) (s: State): Bool :=
  match b with
  | true  => .true
  | false => .false
  | not b => !eval b s
  | and b b' => eval b s && eval b' s
  | or b b'  => eval b s || eval b' s
  | eq a a'  => a s == a' s
  | le a a'  => a s <= a' s

instance: CoeFun Bexp (fun _b => State → Bool) := ⟨eval⟩

instance reduce.equiv: Setoid Bexp where
  r b b':= ∀{s}, b s = b' s
  iseqv := ⟨fun _ => rfl, (Eq.symm .), (Eq.trans . .)⟩

section Equivalence

-- relational definition is equivalent to recursive
private theorem reduce.from_natural {conf: Bexp × State}
  (hBigStep: conf ==>b x): conf.1 conf.2 = x :=
  by induction hBigStep with
  | not _ ih => exact ih ▸ rfl
  | and _ _ ihb ihb' | or _ _ ihb ihb' =>
    exact ihb ▸ ihb' ▸ rfl
  | _ => rfl

private theorem BigStep.from_reduce {b: Bexp}
  (hred: b s = x): (b, s) ==>b x :=
  by induction b generalizing x with
  | true => exact hred ▸ BigStep.true
  | false => exact hred ▸ BigStep.false
  | not _ ih => exact hred ▸ BigStep.not (ih rfl)
  | and _ _ ihb ihb' =>
    exact hred ▸ BigStep.and (ihb rfl) (ihb' rfl)
  | or _ _ ihb ihb' =>
    exact hred ▸ BigStep.or (ihb rfl) (ihb' rfl)
  | eq => exact hred ▸ BigStep.eq
  | le => exact hred ▸ BigStep.le

private theorem BigStep_eq_reduce {b: Bexp}:
  (b, s) ==>b x ↔ b s = x :=
  ⟨reduce.from_natural, BigStep.from_reduce⟩

private theorem BigStep_eq_reduce' {b: Bexp}:
  (b, s) ==>b b s :=
  BigStep.from_reduce rfl

private theorem not_true_eq_false {b: Bexp}: (!b s) = (~~~b) s :=
  rfl

private theorem BigStep_eq_eq_reduce_eq:
  BigStep.equiv.r b b' ↔ reduce.equiv.r b b' := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize @h s (b s)
    rw [BigStep_eq_reduce, BigStep_eq_reduce, eq_self, true_iff] at h
    exact h.symm
  . intro h s n
    specialize @h s
    rw [BigStep_eq_reduce, BigStep_eq_reduce, h]

end Equivalence

end Bexp
