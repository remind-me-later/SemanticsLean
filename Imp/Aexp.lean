import Imp.State
import Imp.Syntax

-- Operational semantics of aexp
inductive 𝔸.evₒ: 𝔸 → Σ → Int → Prop 
  | numₒ (σ: Σ) (n: Int):
    evₒ (num n) σ n

  | locₒ (σ: Σ) (x: String):
    evₒ (loc x) σ (S⟦x⟧ σ)

  | sumₒ (σ: Σ) (a₁ a₂: 𝔸) (n₁ n₂: Int)
    (h₁: evₒ a₁ σ n₁) (h₂: evₒ a₂ σ n₂):
    evₒ ⦃.a₁ + .a₂⦄ σ (n₁ + n₂)

  | prodₒ (σ: Σ) (a₁ a₂: 𝔸) (n₁ n₂: Int)
    (h₁: evₒ a₁ σ n₁) (h₂: evₒ a₂ σ n₂):
    evₒ ⦃.a₁ * .a₂⦄ σ (n₁ * n₂)

notation "⟨" a "," σ "⟩" " → " n => 𝔸.evₒ a σ n

-- Denotational semantics of arithmetic expressions
@[simp] def 𝔸.ev (a: 𝔸) (σ: Σ): Int :=
  match a with
  | num n     => n
  | loc x     => S⟦x⟧ σ
  | ⦃.a₁ + .a₂⦄ => (ev a₁ σ) + (ev a₂ σ)
  | ⦃.a₁ * .a₂⦄ => (ev a₁ σ) * (ev a₂ σ)

notation "⟪" a "," σ "⟫" => 𝔸.ev a σ
 
-- Examples of the semantics of arithmetic expressions.
example: ⟪⦃x⦄, ⟦x↦5⟧⟫ = 5 := rfl
example: ⟪⦃x⦄, ⟦y↦5⟧⟫ = 0 := rfl
example: ⟪⦃4 + 7⦄, ⟦⟧⟫ = 11 := rfl
example: ⟪⦃4 * 7⦄, ⟦⟧⟫ = 28 := rfl

-- relational definition is equivalent to recursive
theorem 𝔸.evₒ_eq_ev (a: 𝔸) (n: Int) (σ: Σ):
  (⟨a, σ⟩ → n) ↔ (⟪a, σ⟫ = n) :=
  by
    apply Iff.intro
    . {
      intro h
      induction h with
      | numₒ _ _ => rfl
      | locₒ _ _ => rfl 
      | sumₒ _ _ _ _ _ _ _ ih₁ ih₂ => rw [←ih₁, ←ih₂]; rfl
      | prodₒ _ _ _ _ _ _ _ ih₁ ih₂ => rw [←ih₁, ←ih₂]; rfl
    }
    . {
      revert n
      induction a with
      | num _ => intro _ h; rw [←h]; constructor
      | loc _ => intro _ h; rw [←h]; constructor
      | sum _ _ ih₁ ih₂ => {
          intro _ h
          rw [←h]
          constructor
          . apply ih₁; rfl
          . apply ih₂; rfl 
        }
      | prod _ _ ih₁ ih₂ => {
          intro _ h
          rw [←h]
          constructor
          . apply ih₁; rfl
          . apply ih₂; rfl
        }
    }

def 𝔸.simₒ (a₁ a₂: 𝔸) :=
  ∀ (σ: Σ) (n: Int), (⟨a₁, σ⟩ → n) ↔ (⟨a₂, σ⟩ → n)

def 𝔸.sim (a₁ a₂: 𝔸) :=
  ∀ σ: Σ, ⟪a₁, σ⟫ = ⟪a₂, σ⟫

theorem 𝔸.simₒ_eq_sim (a₁ a₂: 𝔸):
  (simₒ a₁ a₂) ↔ (sim a₁ a₂) :=
  by 
    apply Iff.intro <;> (intro h; unfold sim at *; unfold simₒ at *)
    . {
      intro σ
      specialize h σ ⟪a₂, σ⟫
      rw [evₒ_eq_ev] at h
      apply h.mpr
      rw [evₒ_eq_ev]
    }
    . {
      intro σ _
      apply Iff.intro <;> {
        intro h₁
        rw [evₒ_eq_ev] at h₁
        rw [evₒ_eq_ev, ←h₁, h]
      }
    }

notation e₁ " ∼ " e₂ => 𝔸.sim e₁ e₂
