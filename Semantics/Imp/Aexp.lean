import Semantics.Imp.Lang

namespace Aexp
namespace BigStep

private inductive BigStep: Aexp × State → Int → Prop
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
  r a a' := ∀{s n}, ((a, s) ==> n) ↔ ((a', s) ==> n)
  iseqv := {
    refl := fun _ => Iff.rfl
    symm := (Iff.symm .)
    trans := (Iff.trans . .)
  }

private example: ((var "x" + 5) + (9 - 7), s0) ==> 7 :=
  .add (.add .var .val) (.sub .val .val)

end BigStep

def eval (a: Aexp) (s: State): Int :=
  match a with
  | val n => n
  | var v => s v
  | add a a' => eval a s + eval a' s
  | sub a a' => eval a s - eval a' s
  | mul a a' => eval a s * eval a' s

instance: CoeFun Aexp (fun _a => State → Int) := ⟨eval⟩

instance reduce.equiv: Setoid Aexp where
  r a a' := ∀{s}, a s = a' s
  iseqv := {
    refl := fun _ => rfl
    symm := (Eq.symm .)
    trans := (Eq.trans . .)
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
  ((a, s) ==> n) ↔ (a s = n) :=
  ⟨reduce.from_natural, BigStep.from_reduce⟩

private theorem BigStep_eq_reduce':
  (a, s) ==> a s :=
  BigStep.from_reduce rfl

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

end Aexp
