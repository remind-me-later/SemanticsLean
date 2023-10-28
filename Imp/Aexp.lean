import Imp.State
import Imp.Syntax

-- Operationaa₁ semantics of aexp
inductive 𝔸.ε: 𝔸 → 𝕊 → Int → Prop
  | num:
    ε (num n) _ n

  | loc:
    ε (loc x) s (𝕊.ρ x s)

  | add (h₁: ε a₁ s n) (h₂: ε a₂ s m):
    ε ⦃a₁ + a₂⦄ s (n + m)

  | mul (h₁: ε a₁ s n) (h₂: ε a₂ s m):
    ε ⦃a₁ * a₂⦄ s (n * m)

-- Denotationaa₁ semantics of arithmetic expressions
@[simp] def 𝔸.ρ (a: 𝔸) (s: 𝕊): Int :=
  match a with
  | num n    => n
  | loc x    => 𝕊.ρ x s
  | ⦃a₁ + r⦄ => (ρ a₁ s) + (ρ r s)
  | ⦃a₁ * r⦄ => (ρ a₁ s) * (ρ r s)

-- Examples of the semantics of arithmetic expressions.
#reduce 𝔸.ρ ⟪x⟫ ⟦x↦5⟧
#reduce 𝔸.ρ ⟪x⟫ ⟦y↦5⟧
#reduce 𝔸.ρ ⟪4 + 7⟫ ⟦⟧
#reduce 𝔸.ρ ⟪4 * 7⟫ ⟦⟧

-- relationaa₁ definition is equivalent to recursive
@[simp↓] theorem 𝔸.ε_iff_ρ:
  ε a s n ↔ ρ a s = n :=
  by
    constructor
    . intro h; induction h with
      | num => rfl
      | loc => rfl
      | _ _ _ ih₁ ih₂ => simp; rw [ih₁, ih₂]
    . revert n; induction a with
      | num _ => intro _ h; cases h; constructor
      | loc _ => intro _ h; cases h; constructor
      | _ _ _ ih₁ ih₂ => {
          intro _ h
          cases h
          constructor
          . apply ih₁; rfl
          . apply ih₂; rfl
        }

def 𝔸.esim a₁ a₂ := ∀ s n, ε a₁ s n ↔ ε a₂ s n

def 𝔸.rsim a₁ a₂ := ∀ s, ρ a₁ s = ρ a₂ s

theorem 𝔸.esim_eq_sim: esim a₁ a₂ ↔ rsim a₁ a₂ :=
  by
    constructor <;> intro h
    . intro s
      specialize h s (ρ a₂ s)
      simp at h
      assumption
    . intro s _
      specialize h s
      simp
      rw [h]
      simp
