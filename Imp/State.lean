inductive 𝕊
  | init : 𝕊
  | update : 𝕊 → String → Int → 𝕊

@[simp] def 𝕊.ρ (x: String) (s: 𝕊): Int :=
  match s with
  | 𝕊.init => 0 -- unbound variables are 0
  | 𝕊.update s₁ x₁ n₁ => if x₁ = x then n₁ else ρ x s₁

instance: Setoid 𝕊 where
  r s₁ s₂ := ∀x, 𝕊.ρ x s₁ = 𝕊.ρ x s₂
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
notation "⟦⟧" => 𝕊.init
notation "⟦" x "↦" e "⟧" => 𝕊.update ⟦⟧ x e
notation s "⟦" x "↦" e "⟧" => 𝕊.update s x e

#check ⟦⟧
#check ⟦"x"↦3⟧⟦"x"↦4⟧
#eval  𝕊.ρ "x" (⟦"x"↦3⟧⟦"x"↦4⟧⟦"x"↦7⟧)
