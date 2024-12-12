import Semantics.Imp.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
private inductive big_step: Bexp × State -> Bool -> Prop
  | true: big_step (true, _) Bool.true
  | false: big_step (false, _) Bool.false
  | not (h: big_step (b, s) x):
    big_step (~~~b, s) (!x)
  | and (h1: big_step (b, s) x) (h2: big_step (b', s) y):
    big_step (b &&& b', s) (x && y)
  | or (h1: big_step (b, s) x) (h2: big_step (b', s) y):
    big_step (b ||| b', s) (x || y)
  | eq: big_step (eq a a', s) (a s == a' s)
  | le: big_step (le a a', s) (a s <= a' s)

infix:10 " ==> " => big_step

private instance big_step.equiv: Setoid Bexp where
  r b b' := ∀{s n}, ((b, s) ==> n) = ((b', s) ==> n)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1 ▸ h2
  }

end Natural

-- Denotational semantics of Bexp
def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | true  => Bool.true
  | false => Bool.false
  | not b => !b.reduce s
  | and b b' => b.reduce s && b'.reduce s
  | or b b'  => b.reduce s || b'.reduce s
  | eq a a'  => a s == a' s
  | le a a'  => a s <= a' s

instance: CoeFun Bexp (fun _ => State -> Bool) := CoeFun.mk reduce

instance reduce.equiv: Setoid Bexp where
  r b b':= ∀{s}, b s = b' s
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1 ▸ h2
  }

section Equivalence

-- relational definition is equivalent to recursive
private theorem reduce.from_natural {conf: Bexp × State}
  (hbig_step: conf ==> x): conf.1 conf.2 = x :=
  by induction hbig_step with
  | not _ ih => exact ih ▸ rfl
  | and _ _ ihb ihb' | or _ _ ihb ihb' =>
    exact ihb ▸ ihb' ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce {b: Bexp}
  (hred: b s = x): (b, s) ==> x :=
  by induction b generalizing x with
  | true => exact hred ▸ big_step.true
  | false => exact hred ▸ big_step.false
  | not _ ih => exact hred ▸ big_step.not (ih rfl)
  | and _ _ ihb ihb' =>
    exact hred ▸ big_step.and (ihb rfl) (ihb' rfl)
  | or _ _ ihb ihb' =>
    exact hred ▸ big_step.or (ihb rfl) (ihb' rfl)
  | eq => exact hred ▸ big_step.eq
  | le => exact hred ▸ big_step.le

private theorem big_step_eq_reduce {b: Bexp}:
  ((b, s) ==> x) = (b s = x) :=
  propext $ Iff.intro reduce.from_natural Natural.from_reduce

private theorem big_step_eq_reduce' {b: Bexp}:
  (b, s) ==> b s :=
  Natural.from_reduce rfl

private theorem not_true_eq_false:
  (!(reduce b s)) = (~~~b) s :=
  rfl

private theorem big_step_eq_eq_reduce_eq:
  Natural.big_step.equiv.r b b' <-> reduce.equiv.r b b' := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . exact fun h => (big_step_eq_reduce ▸ h).mpr $ big_step_eq_reduce.mpr rfl
  . exact fun h => {
      mp := fun h1 => (h ▸ (big_step_eq_reduce ▸ h1)) ▸ big_step_eq_reduce',
      mpr := fun h1 => (h ▸ (big_step_eq_reduce ▸ h1)) ▸ big_step_eq_reduce'
    }

end Equivalence

end Bexp
