inductive State
  | init : State
  | update : State → String → Int → State

@[simp] def State.red (s: State) (x: String): Int :=
  match s with
  | State.init => 0 -- unbound variables are 0
  | State.update s₁ x₁ n₁ => if x₁ = x then n₁ else red s₁ x

infix:110 "↓" => State.red

instance State.equiv: Setoid State where
  r s₁ s₂ := ∀x, s₁↓x = s₂↓x
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

notation "⟦⟧" => State.init
notation "⟦" x "↦" e "⟧" => State.update ⟦⟧ x e
notation s "⟦" x "↦" e "⟧" => State.update s x e

#check ⟦⟧
#check ⟦"x"↦3⟧⟦"x"↦4⟧
#eval  ⟦"x"↦3⟧⟦"x"↦4⟧⟦"x"↦7⟧↓"x"
