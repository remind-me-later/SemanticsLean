import Imp.State
import Imp.Syntax

import Mathlib.Init.Function

-- Operational semantics of aexp
inductive Aexp.Nat: Aexp × State → Int → Prop
  | num₁:
    Nat (num n, _) n

  | loc₁:
    Nat (loc x, s) (s↓x)

  | add₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (add a b, s) (n + m)

  | sub₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (sub a b, s) (n - m)

  | mul₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (mul a b, s) (n * m)

infix:110 " ⟹ " => Aexp.Nat

-- Denotational semantics of arithmetic expressions
@[reducible] def Aexp.red (a: Aexp) (s: State): Int :=
  match a with
  | num n => n
  | loc x => s↓x
  | add a b => red a s + red b s
  | sub a b => red a s - red b s
  | mul a b => red a s * red b s

infix:110 "↓" => Aexp.red

-- relational definition is equal to recursive
theorem Aexp.red.from_Nat (h: as ⟹ n): red.uncurry as = n :=
  by induction h with
  | num₁ => rfl
  | loc₁ => rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

theorem Aexp.Nat.from_red {a: Aexp} (h: a↓s = n): (a,s) ⟹ n :=
  by induction a generalizing n with
  | num _ => exact h ▸ num₁
  | loc _ => exact h ▸ loc₁
  | add _ _ l r => exact h ▸ add₁ (l rfl) (r rfl)
  | sub _ _ l r => exact h ▸ sub₁ (l rfl) (r rfl)
  | mul _ _ l r => exact h ▸ mul₁ (l rfl) (r rfl)

@[simp] theorem Aexp.Nat_iff_red: (a, s) ⟹ n ↔ a↓s = n := ⟨red.from_Nat, Nat.from_red⟩
@[simp] theorem Aexp.Nat_iff_red': (a, s) ⟹ (a↓s) := Nat.from_red rfl

protected instance Aexp.Nat.equiv: Setoid Aexp where
  r a b := ∀ s n, (a, s) ⟹ n = (b, s) ⟹ n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

instance Aexp.red.equiv: Setoid Aexp where
  r := (red · = red ·)
  iseqv := {
    refl := λ _ ↦ Eq.refl _
    symm := (Eq.symm ·)
    trans := (· ▸ ·)
  }

protected theorem Aexp.Nat_eq_eq_red_eq: Aexp.Nat.equiv.r a b ↔ Aexp.red.equiv.r a b :=
  by
  constructor <;> intro h
  . simp [Setoid.r] at *
    apply funext
    intro s
    specialize h s (b↓s)
    simp at h
    exact h
  . simp [Setoid.r] at *
    simp [h]
