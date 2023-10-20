inductive State
  | init : State
  | update : State → String → Int → State

notation "Σ" => State

@[simp] def seval (x: String) (σ: Σ): Int :=
  match σ with
  | State.init => 0 -- unbound variables are 0
  | State.update σ₁ x₁ n₁ => if x₁ = x then n₁ else seval x σ₁

notation "S⟦" x "⟧" => seval x

def state_equiv (σ₁ σ₂: Σ) :=
  ∀ x: String, S⟦x⟧ σ₁ = S⟦x⟧ σ₂ 

notation e₁ " ∼ " e₂ => state_equiv e₁ e₂

declare_syntax_cat state

syntax ident "↦" term : state
syntax state "," ident "↦" term  : state
syntax "⟦""⟧" : term
syntax "⟦" state "⟧" : term
-- meta
-- syntax "." ident "↦" term : state
-- syntax state "," "." ident "↦" term  : state

macro_rules
  | `(⟦⟧)                        => `(State.init)
  | `(⟦$x:ident ↦ $e⟧)      => `(State.update ⟦⟧ $(Lean.quote (toString x.getId)) $e)
  | `(⟦$s , $x:ident ↦ $e⟧) => `(State.update ⟦$s⟧ $(Lean.quote (toString x.getId)) $e)
  -- meta
  -- | `(⟦. $x:ident ↦ $n:num⟧)      => `(State.update ⟦⟧ $x $n)
  -- | `(⟦$s , . $x:ident ↦ $n:num⟧) => `(State.update ⟦$s⟧ $x $n)

#check ⟦⟧
#check ⟦x↦3, x↦4⟧
#eval S⟦"x"⟧ (⟦x↦3, x↦4, x↦7⟧)
