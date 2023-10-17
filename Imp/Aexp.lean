import Imp.State
import Imp.Syntax

-- Operational semantics of aexp
inductive aevalₒₛ: Aexp → Σ → Int → Prop 
  | numₒₛ (σ: Σ) (n: Int):
    aevalₒₛ (nᵢ n) σ n

  | locₒₛ (σ: Σ) (x: String):
    aevalₒₛ (lᵢ x) σ (σ x)

  | sumₒₛ (σ: Σ) (a₁ a₂: Aexp) (n₁ n₂: Int)
    (h₁: aevalₒₛ a₁ σ n₁) (h₂: aevalₒₛ a₂ σ n₂):
    aevalₒₛ (a₁ +ᵢ a₂) σ (n₁ + n₂)

  | prodₒₛ (σ: Σ) (a₁ a₂: Aexp) (n₁ n₂: Int)
    (h₁: aevalₒₛ a₁ σ n₁) (h₂: aevalₒₛ a₂ σ n₂):
    aevalₒₛ (a₁ *ᵢ a₂) σ (n₁ * n₂)

notation "⟨" a "," σ "⟩" " ⟶ " n => aevalₒₛ a σ n

-- Denotational semantics of arithmetic expressions
@[simp] def aeval (a: Aexp) (σ: Σ): Int :=
  match a with
  | nᵢ n     => n
  | lᵢ x     => σ x
  | a₁ +ᵢ a₂ => (aeval a₁ σ) + (aeval a₂ σ)
  | a₁ *ᵢ a₂ => (aeval a₁ σ) * (aeval a₂ σ)

notation "A⟦" a "⟧" => aeval a

-- Examples of the semantics of arithmetic expressions.
example: A⟦⦃x⦄⟧ ⟦"x"↦5⟧ = 5 := rfl
example: A⟦⦃x⦄⟧ ⟦"y"↦5⟧ = 0 := rfl
example: A⟦⦃4 + 7⦄⟧ ⟦⟧ = 11 := rfl
example: A⟦⦃4 * 7⦄⟧ ⟦⟧ = 28 := rfl

-- relational definition is equivalent to recursive
theorem aeval_iff_aevalₒₛ (a: Aexp) (n: Int) (σ: Σ):
  (⟨a, σ⟩ ⟶ n) ↔ A⟦a⟧ σ = n :=
  by
    apply Iff.intro
    case mp => {
      intro h
      induction h with
      | numₒₛ _ _ => rfl
      | locₒₛ _ _ => rfl 
      | sumₒₛ _ _ _ _ _ _ _ ih₁ ih₂ => rw [←ih₁, ←ih₂]; rfl
      | prodₒₛ _ _ _ _ _ _ _ ih₁ ih₂ => rw [←ih₁, ←ih₂]; rfl
    }
    case mpr => {
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
          intros _ h
          rw [←h]
          constructor
          . apply ih₁; rfl
          . apply ih₂; rfl
        }
    }

def aexp_equiv (a₁ a₂: Aexp) :=
  ∀ σ: Σ, A⟦a₁⟧ σ = A⟦a₂⟧ σ

notation e₁ " ∼ " e₂ => aexp_equiv e₁ e₂

#check aexp_equiv

#print axioms aeval_iff_aevalₒₛ
