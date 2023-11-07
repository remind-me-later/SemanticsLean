import Imp.State
import Imp.Syntax

-- Operationaa₁ semantics of aexp
inductive 𝔸.ε: 𝔸 → 𝕊 → Int → Prop
  | num:
    ε (num n) _ n

  | loc:
    ε (loc x) s (𝕊.ρ x s)

  | add (h₁: ε a₁ s n) (h₂: ε a₂ s m):
    ε (a₁ +ₛ a₂) s (n + m)

  | sub (h₁: ε a₁ s n) (h₂: ε a₂ s m):
    ε (a₁ -ₛ a₂) s (n - m)

  | mul (h₁: ε a₁ s n) (h₂: ε a₂ s m):
    ε (a₁ *ₛ a₂) s (n * m)

-- Denotationaa₁ semantics of arithmetic expressions
@[reducible] def 𝔸.ρ (a: 𝔸) (s: 𝕊): Int :=
  match a with
  | num n      => n
  | loc x      => 𝕊.ρ x s
  | a₁ +ₛ a₂ => (ρ a₁ s) + (ρ a₂ s)
  | a₁ -ₛ a₂ => (ρ a₁ s) - (ρ a₂ s)
  | a₁ *ₛ a₂ => (ρ a₁ s) * (ρ a₂ s)

-- Examples of the semantics of arithmetic expressions.
#reduce 𝔸.ρ ⟪x⟫ ⟦x↦5⟧
#reduce 𝔸.ρ ⟪x⟫ ⟦y↦5⟧
#reduce 𝔸.ρ ⟪4 + 7⟫ ⟦⟧
#reduce 𝔸.ρ ⟪4 * 7⟫ ⟦⟧

-- relational definition is equivalent to recursive
@[simp↓] theorem 𝔸.ε_iff_ρ: ε a s n ↔ ρ a s = n :=
  by
    constructor
    . intro h; induction h with
      | num => rfl
      | loc => rfl
      | _ _ _ ih₁ ih₂ => unfold ρ; rw [ih₁, ih₂]
    . revert n; induction a with
      | num _ => intro _ h; cases h; constructor
      | loc _ => intro _ h; cases h; constructor
      | _ _ _ ih₁ ih₂ =>
        intro _ h; cases h; constructor
        . apply ih₁; rfl
        . apply ih₂; rfl

def 𝔸.ε_eq a₁ a₂ := ∀ s n, ε a₁ s n ↔ ε a₂ s n

def 𝔸.ρ_eq a₁ a₂ := ∀ s, ρ a₁ s = ρ a₂ s

theorem 𝔸.ε_eq_iff_ρ_eq: ε_eq a₁ a₂ ↔ ρ_eq a₁ a₂ :=
  by
    constructor <;> intro h s
    . specialize h s (ρ a₂ s)
      simp at h; assumption
    . intro _; simp; rw [h]; simp

instance: Setoid 𝔸 where
  r := 𝔸.ρ_eq
  iseqv := {
    refl := by {
      unfold 𝔸.ρ_eq
      simp
    }
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
