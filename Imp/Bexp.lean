import Imp.State
import Imp.Aexp
import Imp.Syntax

-- Operational semantics of 𝔹
inductive 𝔹.evₒ: 𝔹 → Σ → Bool → Prop 
  | trueₒ (σ: Σ):
    evₒ ⦃tt⦄ σ Bool.true

  | falseₒ (σ: Σ):
    evₒ ⦃ff⦄ σ Bool.false

  | eqₒ (σ: Σ) (a₁ a₂: 𝔸) (n₁ n₂: Int)
    (h₁: ⟨a₁,σ⟩ → n₁) (h₁: ⟨a₂,σ⟩ → n₂):
    evₒ ⦃.a₁ == .a₂⦄ σ (n₁ = n₂)

  | leₒ (σ: Σ) (a₁ a₂: 𝔸) (n₁ n₂: Int)
    (h₁: ⟨a₁,σ⟩ → n₁) (h₁: ⟨a₂,σ⟩ → n₂):
    evₒ ⦃.a₁ <= .a₂⦄ σ (n₁ ≤ n₂)

  | notₒ (σ: Σ) (b₁: 𝔹) (n₁: Bool)
    (h₁: evₒ b₁ σ n₁):
    evₒ ⦃!.b₁⦄ σ (¬n₁)

  | andₒ (σ: Σ) (b₁ b₂: 𝔹) (n₁ n₂: Bool)
    (h₁: evₒ b₁ σ n₁) (h₁: evₒ b₂ σ n₂):
    evₒ ⦃.b₁ && .b₂⦄ σ (n₁ ∧ n₂)

  | orₒ (σ: Σ) (b₁ b₂: 𝔹) (n₁ n₂: Bool)
    (h₁: evₒ b₁ σ n₁) (h₁: evₒ b₂ σ n₂):
    evₒ ⦃.b₁ || .b₂⦄ σ (n₁ ∨ n₂)

notation "⟨" b "," σ "⟩" " → " n => 𝔹.evₒ b σ n
    
-- Denotational semantics of 𝔹
@[simp] def 𝔹.ev (b: 𝔹) (σ: Σ): Bool :=
  match b with
  | ⦃tt⦄        => Bool.true
  | ⦃ff⦄        => Bool.false
  | ⦃.a₁ == .a₂⦄ => ⟪a₁, σ⟫ = ⟪a₂, σ⟫
  | ⦃.a₁ <= .a₂⦄ => ⟪a₁, σ⟫ ≤ ⟪a₂, σ⟫
  | ⦃!.b⦄       => ¬(ev b σ)
  | ⦃.b₁ && .b₂⦄ => (ev b₁ σ) ∧ (ev b₂ σ)
  | ⦃.b₁ || .b₂⦄ => (ev b₁ σ) ∨ (ev b₂ σ)

notation "⟪" b "," σ "⟫" => 𝔹.ev b σ 

--  Examples of the semantics of 𝔹
example: ⟪⦃x <= 5⦄, ⟦x↦5⟧⟫ = true := rfl
example: ⟪⦃x <= 5⦄, ⟦x↦6⟧⟫ = false := rfl
example: ⟪⦃x == 5⦄, ⟦x↦5⟧⟫ = true := rfl
example: ⟪⦃x == 5⦄, ⟦x↦6⟧⟫ = false := rfl
example: ⟪⦃!(x == 5)⦄, ⟦x↦5⟧⟫ = false := rfl

-- relational definition is equivalent to recursive
theorem 𝔹.evₒ_eq_ev (b: 𝔹) (r: Bool) (σ: Σ):
  (⟨b,σ⟩ → r) ↔ ⟪b, σ⟫ = r :=
  by
    apply Iff.intro
    case mp => { 
      intro h; induction h with
      | trueₒ => constructor
      | falseₒ => constructor
      | eqₒ _ _ _ _ _ ih₁ ih₂ => {
          rw [𝔸.evₒ_eq_ev] at ih₁
          rw [𝔸.evₒ_eq_ev] at ih₂
          rw [←ih₁, ←ih₂]
          constructor
        }
      | leₒ _ _ _ _ _ ih₁ ih₂ => {
          rw [𝔸.evₒ_eq_ev] at ih₁;
          rw [𝔸.evₒ_eq_ev] at ih₂;
          rw [←ih₁, ←ih₂]
          constructor
        }
      | notₒ _ _ _ _ ih => {
          rw [←ih]
          constructor
        }
      | andₒ _ _ _ _ _ h₁ h₂ ih₁ ih₂ => {
          induction ih₁; induction ih₂
          rfl        
        }
      | orₒ _ _ _ _ _ h₁ h₂ ih₁ ih₂ => {
          induction ih₁; induction ih₂
          rfl        
        }
    }
    case mpr => {
      revert r
      induction b with 
        | true => intro _ h; rw [←h]; constructor
        | false => intro _ h; rw [←h]; constructor
        | eq _ _ => intro _ h; rw [←h]; constructor <;> rw [𝔸.evₒ_eq_ev]
        | le _ _ => intro _ h; rw [←h]; constructor <;> rw [𝔸.evₒ_eq_ev]
        | not _ ih => {
            intro _ h; rw [←h]; constructor
            apply ih
            rfl
          }
        | and _ _ ih₁ ih₂ => {
          intro _ h; rw [←h]; constructor
          apply ih₁; rfl
          apply ih₂; rfl
        }
        | or _ _ ih₁ ih₂ => {
          intro _ h; rw [←h]; constructor
          apply ih₁; rfl
          apply ih₂; rfl
        }
    }

theorem 𝔹.not_true_eq_false (b: 𝔹) (σ: Σ) :
  ⟪b, σ⟫ = Bool.false ↔ ⟪⦃!.b⦄, σ⟫ = Bool.true :=
  by apply Iff.intro <;> (simp; intros; assumption)

def 𝔹.sim (b₁ b₂: 𝔹) :=
  ∀ σ: Σ, ⟪b₁, σ⟫ = ⟪b₂, σ⟫

notation e₁ " ∼ " e₂ => 𝔹.sim e₁ e₂
