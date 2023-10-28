inductive 𝕊
  | init : 𝕊
  | update : 𝕊 → String → Int → 𝕊

@[simp] def 𝕊.ρ (x: String) (s: 𝕊): Int :=
  match s with
  | 𝕊.init => 0 -- unbound variables are 0
  | 𝕊.update s₁ x₁ n₁ => if x₁ = x then n₁ else ρ x s₁

def 𝕊.sim s₁ s₂ := ∀x, ρ x s₁ = ρ x s₂

declare_syntax_cat state

syntax ident "↦" term : state
syntax state "," ident "↦" term  : state
syntax "⟦""⟧" : term
syntax "⟦" state "⟧" : term

macro_rules
  | `(⟦⟧)                        => `(𝕊.init)
  | `(⟦$x:ident ↦ $e⟧)      => `(𝕊.update ⟦⟧ $(Lean.quote (toString x.getId)) $e)
  | `(⟦$s , $x:ident ↦ $e⟧) => `(𝕊.update ⟦$s⟧ $(Lean.quote (toString x.getId)) $e)
  -- meta
  -- | `(⟦. $x:ident ↦ $n:num⟧)      => `(𝕊.update ⟦⟧ $x $n)
  -- | `(⟦$s , . $x:ident ↦ $n:num⟧) => `(𝕊.update ⟦$s⟧ $x $n)

#check ⟦⟧
#check ⟦x↦3, x↦4⟧
#eval 𝕊.ρ "x" (⟦x↦3, x↦4, x↦7⟧)
