import Imp.State
import Imp.Aexp
import Imp.Syntax

-- Operational semantics of 𝔹
inductive 𝔹.ε: 𝔹 → 𝕊 → Bool → Prop
  | tt:
    ε ⦃tt⦄ s true

  | ff:
    ε ⦃ff⦄ s false

  | not (h: ε b₁ s n₁):
    ε ⦃¬b₁⦄ s (¬n₁)

  | and (hₗ: ε b₁ s n₁) (hᵣ: ε b₂ s n₂):
    ε ⦃b₁ ∧ b₂⦄ s (n₁ ∧ n₂)

  | or (hₗ : ε b₁ s n₁) (hᵣ: ε b₂ s n₂):
    ε ⦃b₁ ∨ b₂⦄ s (n₁ ∨ n₂)

  | eq (hₗ: 𝔸.ρ a₁ s = n₁) (hᵣ: 𝔸.ρ a₂ s = n₂):
    ε ⦃a₁ = a₂⦄ s (n₁ = n₂)

  | le (hₗ: 𝔸.ρ a₁ s = n₁) (hᵣ: 𝔸.ρ a₂ s = n₂):
    ε ⦃a₁ ≤ a₂⦄ s (n₁ ≤ n₂)

-- Denotational semantics of 𝔹
@[simp] def 𝔹.ρ (b: 𝔹) (s: 𝕊): Bool :=
  match b with
  | ⦃tt⦄      => true
  | ⦃ff⦄      => false
  | ⦃¬b⦄      => ¬(ρ b s)
  | ⦃b₁ ∧ b₂⦄ => (ρ b₁ s) ∧ (ρ b₂ s)
  | ⦃b₁ ∨ b₂⦄ => (ρ b₁ s) ∨ (ρ b₂ s)
  | ⦃a₁ = a₂⦄ => 𝔸.ρ a₁ s = 𝔸.ρ a₂ s
  | ⦃a₁ ≤ a₂⦄ => 𝔸.ρ a₁ s ≤ 𝔸.ρ a₂ s

--  Examples of the semantics of 𝔹
#reduce 𝔹.ρ ⟪x ≤ 5⟫ ⟦x↦5⟧
#reduce 𝔹.ρ ⟪x ≤ 5⟫ ⟦x↦6⟧
#reduce 𝔹.ρ ⟪x = 5⟫ ⟦x↦5⟧
#reduce 𝔹.ρ ⟪x = 5⟫ ⟦x↦6⟧
#reduce 𝔹.ρ ⟪¬(x = 5)⟫ ⟦x↦5⟧

-- relational definition is equivalent to recursive
@[simp↓] theorem 𝔹.ε_iff_ρ: ε b s r ↔ ρ b s = r :=
  by
    constructor
    . intro h; induction h with
      | tt => rfl
      | ff => rfl
      | eq ih₁ ih₂ => simp at *; cases ih₁; cases ih₂; rfl
      | le ih₁ ih₂ => simp at *; cases ih₁; cases ih₂; rfl
      | not _ ih => simp at *; cases ih; rfl
      | _ _ _ ih₁ ih₂ => cases ih₁; cases ih₂; rfl
    . revert r
      induction b with
        | tt => intro _ h; cases h; constructor
        | ff => intro _ h; cases h; constructor
        | eq _ _ => intro _ h; cases h; constructor <;> simp
        | le _ _ => intro _ h; cases h; constructor <;> simp
        | not _ ih => {
            intro _ h; cases h; constructor
            apply ih
            rfl
          }
        | _ _ _ ih₁ ih₂ => {
          intro _ h; cases h; constructor
          . apply ih₁; rfl
          . apply ih₂; rfl
        }

theorem 𝔹.not_true_eq_false:
  ρ b s = false ↔ ρ ⦃¬b⦄ s = true := by simp

def 𝔹.sim b₁ b₂ := ∀ s, ρ b₁ s = ρ b₂ s
