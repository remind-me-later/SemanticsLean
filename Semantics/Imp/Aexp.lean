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

private instance equiv: Setoid Aexp where
  r a a' := ∀{s n}, ((a, s) ==> n) = ((a', s) ==> n)
  iseqv := {
    refl := fun _ => rfl
    symm := (Eq.symm .)
    trans := (. ▸ .)
  }

private example: ((var "x" + 5) + (9 - 7), s0) ==> 7 :=
  .add (.add .var .val) (.sub .val .val)

end BigStep

def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val n => n
  | var v => s v
  | add a a' => reduce a s + reduce a' s
  | sub a a' => reduce a s - reduce a' s
  | mul a a' => reduce a s * reduce a' s

instance: CoeFun Aexp (fun _a => State -> Int) := ⟨reduce⟩

instance reduce.equiv: Setoid Aexp where
  r a a' := ∀{s}, a s = a' s
  iseqv := {
    refl := fun _ => rfl
    symm := (Eq.symm .)
    trans := (. ▸ .)
  }

#eval (var "x" + 5) + (9 - 7) $ s0 -- 7

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
  | val a => exact hred ▸ .val
  | var a => exact hred ▸ .var
  | add a a' iha iha' =>
    exact hred ▸ (iha rfl).add (iha' rfl)
  | sub a a' iha iha' =>
    exact hred ▸ (iha rfl).sub (iha' rfl)
  | mul a a' iha iha' =>
    exact hred ▸ (iha rfl).mul (iha' rfl)

private theorem BigStep_eq_reduce:
  ((a, s) ==> n) = (a s = n) :=
  propext ⟨reduce.from_natural, BigStep.from_reduce⟩

private theorem BigStep_eq_reduce':
  (a, s) ==> a s :=
  BigStep.from_reduce rfl

private theorem BigStep_eq_eq_reduce_eq:
  BigStep.equiv.r b b' <-> reduce.equiv.r b b' := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . exact fun h => Iff.mpr (BigStep_eq_reduce ▸ h) (Eq.mpr BigStep_eq_reduce rfl)
  . exact fun h => {
      mp := fun h1 => (h ▸ (BigStep_eq_reduce ▸ h1)) ▸ BigStep_eq_reduce',
      mpr := fun h1 => (h ▸ (BigStep_eq_reduce ▸ h1)) ▸ BigStep_eq_reduce'
    }

end Equivalence

end Aexp
