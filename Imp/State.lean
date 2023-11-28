import Mathlib.Logic.Function.Basic

def State := String → Int
def State.nil: State := λ _ ↦ 0

notation "⟪⟫" => State.nil
notation s "⟪" x "≔" e "⟫" => Function.update s x e

#eval ⟪⟫ "x"
#eval (⟪⟫⟪"x" ≔ 3⟫⟪"x" ≔ 4⟫) "x"
#eval (⟪⟫⟪"x" ≔ 3⟫⟪"x" ≔ 4⟫⟪"x" ≔ 7⟫) "x"

theorem State.demo₁: (⟪⟫⟪"x"≔3⟫) = (⟪⟫⟪"x"≔4⟫⟪"x"≔3⟫) := by simp
