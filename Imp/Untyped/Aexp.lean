import Imp.State
import Imp.Untyped.Syntax

import Mathlib.Init.Function

namespace Aexp

-- Operational semantics of aexp
inductive Nat: Aexp × State → Val → Prop
  | num₁:
    Nat (num n, _) n

  | loc₁:
    Nat (loc x, s) (s x)

  | add₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (add a b, s) (n + m)

  | sub₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (sub a b, s) (n - m)

  | mul₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (mul a b, s) (n * m)

infix:110 " ⟹ " => Nat

-- Denotational semantics of arithmetic expressions
@[reducible] def red (a: Aexp) (s: State): Val :=
  match a with
  | num n => n
  | loc x => s x
  | add a b => red a s + red b s
  | sub a b => red a s - red b s
  | mul a b => red a s * red b s

infix:110 "⇓" => red

-- relational definition is equal to recursive
theorem red.from_Nat (h: as ⟹ n): red.uncurry as = n :=
  by induction h with
  | num₁ => rfl
  | loc₁ => rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

theorem Nat.from_red {a: Aexp} (h: a⇓s = n): (a,s) ⟹ n :=
  by induction a generalizing n with
  | num _ => exact h ▸ num₁
  | loc _ => exact h ▸ loc₁
  | add _ _ l r => exact h ▸ add₁ (l rfl) (r rfl)
  | sub _ _ l r => exact h ▸ sub₁ (l rfl) (r rfl)
  | mul _ _ l r => exact h ▸ mul₁ (l rfl) (r rfl)

@[simp] theorem Nat_iff_red: (a, s) ⟹ n ↔ a⇓s = n := ⟨red.from_Nat, Nat.from_red⟩
@[simp] theorem Nat_iff_red': (a, s) ⟹ (a⇓s) := Nat.from_red rfl

protected instance Nat.equiv: Setoid Aexp where
  r a b := ∀ s n, (a, s) ⟹ n = (b, s) ⟹ n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

instance red.equiv: Setoid Aexp := ⟨(red · = red ·), ⟨(Eq.refl $ red ·), Eq.symm, Eq.trans⟩⟩

protected theorem Nat_eq_eq_red_eq: Nat.equiv.r a b ↔ red.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    apply funext
    intro s
    specialize h s
    exact h
  . simp [Setoid.r] at *
    simp [h]

end Aexp