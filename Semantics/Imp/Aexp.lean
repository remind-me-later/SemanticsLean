import Semantics.Imp.Lang

namespace Aexp
namespace Natural

private inductive big_step: Aexp × State -> Int -> Prop
  | val: big_step (val n, _) n
  | var: big_step (var v, s) (s v)
  | add (ha: big_step (a, s) x) (ha': big_step (a', s) y):
    big_step (a + a', s) (x + y)
  | sub (ha: big_step (a, s) x) (ha': big_step (a', s) y):
    big_step (a - a', s) (x - y)
  | mul (ha: big_step (a, s) x) (ha': big_step (a', s) y):
    big_step (a * a', s) (x * y)

infix:10 " ==> " => big_step

private instance big_step.equiv: Setoid Aexp where
  r a a' := ∀{s n}, ((a, s) ==> n) = ((a', s) ==> n)
  iseqv := {
    refl := fun _ => rfl
    symm := (Eq.symm .)
    trans := (. ▸ .)
  }

private example: ((var "x" + 5) + (9 - 7), s0) ==> 7 :=
  big_step.add
    (big_step.add big_step.var big_step.val)
    (big_step.sub big_step.val big_step.val)

end Natural

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
  (hbig_step: conf ==> n): conf.1 conf.2 = n :=
  by induction hbig_step with
  | add _ _ iha iha' => exact iha ▸ iha' ▸ rfl
  | sub _ _ iha iha' => exact iha ▸ iha' ▸ rfl
  | mul _ _ iha iha' => exact iha ▸ iha' ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce
  (hred: a s = n): (a, s) ==> n :=
  by induction a generalizing n with
  | val a => exact hred ▸ big_step.val
  | var a => exact hred ▸ big_step.var
  | add a a' iha iha' =>
    exact hred ▸ big_step.add (iha rfl) (iha' rfl)
  | sub a a' iha iha' =>
    exact hred ▸ big_step.sub (iha rfl) (iha' rfl)
  | mul a a' iha iha' =>
    exact hred ▸ big_step.mul (iha rfl) (iha' rfl)

private theorem big_step_eq_reduce:
  ((a, s) ==> n) = (a s = n) :=
  propext (Iff.intro reduce.from_natural Natural.from_reduce)

private theorem big_step_eq_reduce':
  (a, s) ==> a s :=
  Natural.from_reduce rfl

private theorem big_step_eq_eq_reduce_eq:
  Natural.big_step.equiv.r a a' <-> reduce.equiv.r a a' := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize @h s (a' s)
    rw [big_step_eq_reduce, big_step_eq_reduce, eq_self, iff_true] at h
    exact h
  . intro h s _
    rw [big_step_eq_reduce, big_step_eq_reduce]
    specialize @h s
    rw [h]

end Equivalence

end Aexp
