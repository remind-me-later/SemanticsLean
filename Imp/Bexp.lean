import Imp.State
import Imp.Aexp
import Imp.Syntax

-- Operational semantics of bexp
inductive bevalₒₛ: Bexp → Σ → Bool → Prop 
  | trueₒₛ (σ: Σ):
    bevalₒₛ trueᵢ σ true

  | falseₒₛ (σ: Σ):
    bevalₒₛ falseᵢ σ false

  | eqₒₛ (σ: Σ) (a₁ a₂: Aexp) (n₁ n₂: Int)
    (h₁: ⟨a₁,σ⟩ ⟶ n₁) (h₁: ⟨a₂,σ⟩ ⟶ n₂):
    bevalₒₛ (a₁ =ᵢ a₂) σ (n₁ = n₂)

  | leₒₛ (σ: Σ) (a₁ a₂: Aexp) (n₁ n₂: Int)
    (h₁: ⟨a₁,σ⟩ ⟶ n₁) (h₁: ⟨a₂,σ⟩ ⟶ n₂):
    bevalₒₛ (a₁ ≤ᵢ a₂) σ (n₁ ≤ n₂)

  | notₒₛ (σ: Σ) (b₁: Bexp) (n₁: Bool)
    (h₁: bevalₒₛ b₁ σ n₁):
    bevalₒₛ (¬ᵢb₁) σ (¬n₁)

  | andₒₛ (σ: Σ) (b₁ b₂: Bexp) (n₁ n₂: Bool)
    (h₁: bevalₒₛ b₁ σ n₁) (h₁: bevalₒₛ b₂ σ n₂):
    bevalₒₛ (b₁ ∧ᵢ b₂) σ (n₁ ∧ n₂)

  | orₒₛ (σ: Σ) (b₁ b₂: Bexp) (n₁ n₂: Bool)
    (h₁: bevalₒₛ b₁ σ n₁) (h₁: bevalₒₛ b₂ σ n₂):
    bevalₒₛ (b₁ ∨ᵢ b₂) σ (n₁ ∨ n₂)

notation "⟨" b "," σ "⟩" " ⟶ " n => bevalₒₛ b σ n
    
-- Denotational semantics of boolean expressions
@[simp] def beval (b: Bexp) (σ: Σ): Bool :=
  match b with 
  | trueᵢ    => true
  | falseᵢ   => false
  | a₁ =ᵢ a₂ => A⟦a₁⟧ σ = A⟦a₂⟧ σ
  | a₁ ≤ᵢ a₂ => A⟦a₁⟧ σ ≤ A⟦a₂⟧ σ
  | ¬ᵢb      => ¬(beval b σ)
  | b₁ ∧ᵢ b₂ => (beval b₁ σ) ∧ (beval b₂ σ)
  | b₁ ∨ᵢ b₂ => (beval b₁ σ) ∨ (beval b₂ σ)

notation " B⟦" b "⟧" => beval b

--  Examples of the semantics of boolean expressions.
example: B⟦⦃x ≤ 5⦄⟧ ⟦"x"↦5⟧ = true := rfl
example: B⟦⦃x ≤ 5⦄⟧ ⟦"x"↦6⟧ = false := rfl
example: B⟦⦃x = 5⦄⟧ ⟦"x"↦5⟧ = true := rfl
example: B⟦⦃x = 5⦄⟧ ⟦"x"↦6⟧ = false := rfl
example: B⟦⦃¬(x = 5)⦄⟧ ⟦"x"↦5⟧ = false := rfl

-- relational definition is equivalent to recursive
theorem beval_iff_bevalₒₛ (b: Bexp) (r: Bool) (σ: Σ):
  (⟨b,σ⟩ ⟶ r) ↔ B⟦b⟧ σ = r :=
  by
    apply Iff.intro
    case mp => { 
      intro h; induction h with
      | trueₒₛ => constructor
      | falseₒₛ => constructor
      | eqₒₛ _ _ _ _ _ ih₁ ih₂ => {
          rw [aeval_iff_aevalₒₛ] at ih₁
          rw [aeval_iff_aevalₒₛ] at ih₂
          rw [←ih₁, ←ih₂]
          constructor
        }
      | leₒₛ _ _ _ _ _ ih₁ ih₂ => {
          rw [aeval_iff_aevalₒₛ] at ih₁;
          rw [aeval_iff_aevalₒₛ] at ih₂;
          rw [←ih₁, ←ih₂]
          constructor
        }
      | notₒₛ _ _ _ _ ih => {
          rw [←ih]
          constructor
        }
      | andₒₛ _ _ _ _ _ h₁ h₂ ih₁ ih₂ => {
          induction ih₁; induction ih₂
          rfl        
        }
      | orₒₛ _ _ _ _ _ h₁ h₂ ih₁ ih₂ => {
          induction ih₁; induction ih₂
          rfl        
        }
    }
    case mpr => {
      revert r
      induction b with 
        | true => intro _ h; rw [←h]; constructor
        | false => intro _ h; rw [←h]; constructor
        | eq _ _ => intro _ h; rw [←h]; constructor <;> rw [aeval_iff_aevalₒₛ]
        | le _ _ => intro _ h; rw [←h]; constructor <;> rw [aeval_iff_aevalₒₛ]
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

theorem beval_not_true_iff_false (b: Bexp) (σ: Σ) :
  B⟦b⟧ σ = false ↔ B⟦¬ᵢb⟧ σ = true :=
  by apply Iff.intro <;> (simp; intros; assumption)

def bexp_equiv (b₁ b₂: Bexp) :=
  ∀ σ: Σ, B⟦b₁⟧ σ = B⟦b₂⟧ σ

notation e₁ " ∼ " e₂ => bexp_equiv e₁ e₂
