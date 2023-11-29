import Imp.State
import Imp.Untyped.Syntax

import Mathlib.Init.Function

namespace Aexp

-- Operational semantics of aexp
inductive Natural: Aexp × State → Val → Prop
  | num₁:
    Natural (num n, _) n

  | loc₁:
    Natural (loc x, s) (s x)

  | add₁ (h₁: Natural (a,s) n) (h₂: Natural (b,s) m):
    Natural (add a b, s) (n + m)

  | sub₁ (h₁: Natural (a,s) n) (h₂: Natural (b,s) m):
    Natural (sub a b, s) (n - m)

  | mul₁ (h₁: Natural (a,s) n) (h₂: Natural (b,s) m):
    Natural (mul a b, s) (n * m)

infix:110 " ⟹ " => Natural

-- Denotational semantics of arithmetic expressions
@[reducible]
def reduce (a: Aexp) (s: State): Val :=
  match a with
  | num n => n
  | loc x => s x
  | add a b => reduce a s + reduce b s
  | sub a b => reduce a s - reduce b s
  | mul a b => reduce a s * reduce b s

infix:110 "⇓" => reduce

-- relational definition is equal to recursive
theorem reduce.from_Natural (h: as ⟹ n): reduce.uncurry as = n :=
  by induction h with
  | num₁ => rfl
  | loc₁ => rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

theorem Natural.from_reduce {a: Aexp} (h: a⇓s = n): (a,s) ⟹ n :=
  by induction a generalizing n with
  | num _ => exact h ▸ num₁
  | loc _ => exact h ▸ loc₁
  | add _ _ l r => exact h ▸ add₁ (l rfl) (r rfl)
  | sub _ _ l r => exact h ▸ sub₁ (l rfl) (r rfl)
  | mul _ _ l r => exact h ▸ mul₁ (l rfl) (r rfl)

@[simp] theorem Natural_iff_reduce: (a, s) ⟹ n ↔ a⇓s = n := ⟨reduce.from_Natural, Natural.from_reduce⟩
@[simp] theorem Natural_iff_reduce': (a, s) ⟹ (a⇓s) := Natural.from_reduce rfl

protected instance Natural.equiv: Setoid Aexp where
  r a b := ∀ s n, (a, s) ⟹ n = (b, s) ⟹ n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

instance reduce.equiv: Setoid Aexp where
  r a b := ∀s, a⇓s = b⇓s
  iseqv := ⟨λ _ _ ↦ Eq.refl _, (Eq.symm $ · ·) , λ h₁ h₂ s ↦ (h₁ s) ▸ (h₂ s)⟩

protected theorem Natural_eq_eq_reduce_eq: Natural.equiv.r a b ↔ reduce.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    intro s
    specialize h s
    exact h
  . simp [Setoid.r] at *
    simp [h]

end Aexp
