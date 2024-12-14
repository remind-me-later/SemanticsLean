import Semantics.Imp.Aexp

namespace Bexp
namespace BigStep

-- Operational semantics of Bexp
private inductive BigStep: Bexp × State -> Bool -> Prop
  | true: BigStep (true, _) Bool.true
  | false: BigStep (false, _) Bool.false
  | not (h: BigStep (b, s) x):
    BigStep (~~~b, s) (!x)
  | and (h1: BigStep (b, s) x) (h2: BigStep (b', s) y):
    BigStep (b &&& b', s) (x && y)
  | or (h1: BigStep (b, s) x) (h2: BigStep (b', s) y):
    BigStep (b ||| b', s) (x || y)
  | eq: BigStep (eq a a', s) (a s == a' s)
  | le: BigStep (le a a', s) (a s <= a' s)

infix:10 " ==> " => BigStep

private instance BigStep.equiv: Setoid Bexp where
  r b b' := ∀{s n}, ((b, s) ==> n) = ((b', s) ==> n)
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => Eq.symm h
    trans := fun h1 h2 => h1 ▸ h2
  }

end BigStep

-- Denotational semantics of Bexp
def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | true  => Bool.true
  | false => Bool.false
  | not b => !reduce b s
  | and b b' => reduce b s && reduce b' s
  | or b b'  => reduce b s || reduce b' s
  | eq a a'  => a s == a' s
  | le a a'  => a s <= a' s

instance: CoeFun Bexp (fun _ => State -> Bool) := CoeFun.mk reduce

instance reduce.equiv: Setoid Bexp where
  r b b':= ∀{s}, b s = b' s
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => Eq.symm h
    trans := fun h1 h2 => h1 ▸ h2
  }

section Equivalence

-- relational definition is equivalent to recursive
private theorem reduce.from_natural {conf: Bexp × State}
  (hBigStep: conf ==> x): conf.1 conf.2 = x :=
  by induction hBigStep with
  | not _ ih => exact ih ▸ rfl
  | and _ _ ihb ihb' | or _ _ ihb ihb' =>
    exact ihb ▸ ihb' ▸ rfl
  | _ => rfl

private theorem BigStep.from_reduce {b: Bexp}
  (hred: b s = x): (b, s) ==> x :=
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
  ((b, s) ==> x) = (b s = x) :=
  propext (Iff.intro reduce.from_natural BigStep.from_reduce)

private theorem BigStep_eq_reduce' {b: Bexp}:
  (b, s) ==> b s :=
  BigStep.from_reduce rfl

private theorem not_true_eq_false:
  (!(reduce b s)) = (~~~b) s :=
  rfl

private theorem BigStep_eq_eq_reduce_eq:
  BigStep.BigStep.equiv.r b b' <-> reduce.equiv.r b b' := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . exact fun h => Iff.mpr (BigStep_eq_reduce ▸ h) (Eq.mpr BigStep_eq_reduce rfl)
  . exact fun h => {
      mp := fun h1 => (h ▸ (BigStep_eq_reduce ▸ h1)) ▸ BigStep_eq_reduce',
      mpr := fun h1 => (h ▸ (BigStep_eq_reduce ▸ h1)) ▸ BigStep_eq_reduce'
    }

end Equivalence

end Bexp
