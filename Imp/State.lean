inductive 𝕊
  | init : 𝕊
  | update : 𝕊 → String → Int → 𝕊

@[simp] def 𝕊.red (s: 𝕊) (x: String): Int :=
  match s with
  | 𝕊.init => 0 -- unbound variables are 0
  | 𝕊.update s₁ x₁ n₁ => if x₁ = x then n₁ else red s₁ x

infix:110 "↓" => 𝕊.red

instance 𝕊.equiv: Setoid 𝕊 where
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

notation "⟦⟧" => 𝕊.init
notation "⟦" x "↦" e "⟧" => 𝕊.update ⟦⟧ x e
notation s "⟦" x "↦" e "⟧" => 𝕊.update s x e

#check ⟦⟧
#check ⟦"x"↦3⟧⟦"x"↦4⟧
#eval  ⟦"x"↦3⟧⟦"x"↦4⟧⟦"x"↦7⟧↓"x"
