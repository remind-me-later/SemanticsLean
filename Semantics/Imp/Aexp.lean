import Semantics.Imp.Lang

namespace Aexp
namespace BigStep

private inductive BigStep: Aexp × State -> Int -> Prop
  | val: BigStep (val n, _) n
  | var: BigStep (var v, s) (s v)
  | add (ha: BigStep (a, s) x) (ha': BigStep (a', s) y):
    BigStep (a + a', s) (x + y)
  | sub (ha: BigStep (a, s) x) (ha': BigStep (a', s) y):
    BigStep (a - a', s) (x - y)
  | mul (ha: BigStep (a, s) x) (ha': BigStep (a', s) y):
    BigStep (a * a', s) (x * y)

infix:10 " ==> " => BigStep

private instance BigStep.equiv: Setoid Aexp where
  r a a' := ∀{s n}, ((a, s) ==> n) = ((a', s) ==> n)
  iseqv := {
    refl := fun _ => rfl
    symm := (Eq.symm .)
    trans := (. ▸ .)
  }

private example: ((var "x" + 5) + (9 - 7), s0) ==> 7 :=
  BigStep.add
    (BigStep.add BigStep.var BigStep.val)
    (BigStep.sub BigStep.val BigStep.val)

end BigStep

def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val n => n
  | var v => s v
  | add a a' => reduce a s + reduce a' s
  | sub a a' => reduce a s - reduce a' s
  | mul a a' => reduce a s * reduce a' s

instance: CoeFun Aexp (fun _ => State -> Int) := CoeFun.mk reduce

instance reduce.equiv: Setoid Aexp where
  r a a' := ∀{s}, a s = a' s
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1 ▸ h2
  }

#eval ((var "x" + 5) + (9 - 7)) s0 -- 7

section Equivalence

-- relational definition is equal to recursive
private theorem reduce.from_natural
  (hBigStep: conf ==> n): conf.1 conf.2 = n :=
  by induction hBigStep with
  | add _ _ iha iha' => exact iha ▸ iha' ▸ rfl
  | sub _ _ iha iha' => exact iha ▸ iha' ▸ rfl
  | mul _ _ iha iha' => exact iha ▸ iha' ▸ rfl
  | _ => rfl

private theorem BigStep.from_reduce
  (hred: a s = n): (a, s) ==> n :=
  by induction a generalizing n with
  | val a => exact hred ▸ BigStep.val
  | var a => exact hred ▸ BigStep.var
  | add a a' iha iha' =>
    exact hred ▸ BigStep.add (iha rfl) (iha' rfl)
  | sub a a' iha iha' =>
    exact hred ▸ BigStep.sub (iha rfl) (iha' rfl)
  | mul a a' iha iha' =>
    exact hred ▸ BigStep.mul (iha rfl) (iha' rfl)

private theorem BigStep_eq_reduce:
  ((a, s) ==> n) = (a s = n) :=
  propext (Iff.intro reduce.from_natural BigStep.from_reduce)

private theorem BigStep_eq_reduce':
  (a, s) ==> a s :=
  BigStep.from_reduce rfl

private theorem BigStep_eq_eq_reduce_eq:
  BigStep.BigStep.equiv.r a a' <-> reduce.equiv.r a a' := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize @h s (a' s)
    rw [BigStep_eq_reduce, BigStep_eq_reduce, eq_self, iff_true] at h
    exact h
  . intro h s _
    rw [BigStep_eq_reduce, BigStep_eq_reduce]
    specialize @h s
    rw [h]

end Equivalence

end Aexp
