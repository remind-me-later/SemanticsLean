import Imp.State
import Imp.Syntax

import Mathlib.Init.Function

-- Operational semantics of aexp
inductive 𝔸.Nat: 𝔸 × 𝕊 → Int → Prop
  | num₁:
    Nat (num n, _) n

  | loc₁:
    Nat (loc x, s) (s↓x)

  | add₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (a + b, s) (n + m)

  | sub₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (a - b, s) (n - m)

  | mul₁ (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (a * b, s) (n * m)

infix:110 " ⟹ " => 𝔸.Nat

-- Denotational semantics of arithmetic expressions
@[reducible] def 𝔸.red (a: 𝔸) (s: 𝕊): Int :=
  match a with
  | num n => n
  | loc x => s↓x
  | a + b => red a s + red b s
  | a - b => red a s - red b s
  | a * b => red a s * red b s

infix:110 "↓" => 𝔸.red

-- relational definition is equal to recursive
@[simp] theorem 𝔸.red.from_Nat (h: as ⟹ n): red.uncurry as = n :=
  by induction h with
  | num₁ => unfold Function.uncurry red; rfl
  | loc₁ => unfold Function.uncurry red; rfl
  | _ _ _ ih₁ ih₂ => unfold Function.uncurry red; exact ih₁ ▸ ih₂ ▸ rfl

@[simp] theorem 𝔸.Nat.from_red {a: 𝔸} (h: a↓s = n): (a,s) ⟹ n :=
  by induction a generalizing n with
  | num _ => cases h; unfold red; exact num₁
  | loc _ => cases h; unfold red; exact loc₁
  | add _ _ l r => cases h; unfold red; exact add₁ (l rfl) (r rfl)
  | sub _ _ l r => cases h; unfold red; exact sub₁ (l rfl) (r rfl)
  | mul _ _ l r => cases h; unfold red; exact mul₁ (l rfl) (r rfl)

@[simp] theorem 𝔸.Nat_iff_red: (a,s) ⟹ n ↔ a↓s = n := ⟨red.from_Nat, Nat.from_red⟩
@[simp] theorem 𝔸.Nat_iff_red': (a,s) ⟹ (a↓s) := Nat.from_red rfl

protected instance 𝔸.Nat.equiv: Setoid 𝔸 where
  r a b := ∀ s n, (a,s) ⟹ n ↔ (b,s) ⟹ n
  iseqv := {
    refl := by simp
    symm := by {
      intro _ _ h _ _
      apply Iff.symm
      apply h
    }
    trans := by {
      intro _ _ _ h₁ h₂ x _
      specialize h₁ x
      specialize h₂ x
      rw [h₁, h₂]
    }
  }

instance 𝔸.red.equiv: Setoid 𝔸 where
  r a b := ∀ s, a↓s = b↓s
  iseqv := {
    refl := by simp
    symm := by {
      intro _ _ h _
      apply Eq.symm
      apply h
    }
    trans := by {
      intro _ _ _ h₁ h₂ x
      specialize h₁ x
      specialize h₂ x
      rw [h₁, h₂]
    }
  }

protected theorem 𝔸.Nat_eq_eq_red_eq: 𝔸.Nat.equiv.r a b ↔ 𝔸.red.equiv.r a b :=
  by
    constructor <;> intro h s
    . specialize h s (b↓s)
      simp at h; rw [h]
    . simp; rw [h]; simp
