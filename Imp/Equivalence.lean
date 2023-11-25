import Imp.Natural
import Imp.Structural

theorem ℂ.ε_imp_τ {cs: ℂ × 𝕊} (h: cs ⟹ t): cs ⇒* (skip, t) :=
  by {
    induction h with
    | skip₁ => exact Relation.ReflTransGen.refl
    | ass₁ => exact Relation.ReflTransGen.single (γ.ass₁)
    | cat₁ _ _ _ ihc ihd  => apply τ.cat _ ihc ihd
    | ife₁ hb _ ih =>
      rename_i c _  s _ _
      apply Relation.ReflTransGen.head
      . apply γ.ife₁
        assumption
      . assumption
    | ife₂ hb _ ih =>
      rename_i c d s _ _
      apply Relation.ReflTransGen.head
      . apply γ.ife₂
        assumption
      . assumption
    | wle₁ hb _ _ _ ihc ihw => {
      rename_i b c _ d s _ _
      apply Relation.ReflTransGen.head
      . apply γ.wle₁
      . apply Relation.ReflTransGen.head
        . constructor
          assumption
        . apply τ.cat _ ihc ihw
    }
    | wle₂ => {
      rename_i b c s hb
      apply Relation.ReflTransGen.head
      . apply γ.wle₁
      . apply Relation.ReflTransGen.head
        . apply γ.ife₂
          assumption
        . constructor
    }
  }

lemma ℂ.ε_imp_γ_imp_ε (h₁: cs₀ ⇒ cs₁) (h₂: cs₁ ⟹ s₂): cs₀ ⟹ s₂ :=
  by
  induction h₁ generalizing s₂ with
  | ass₁ => cases h₂; exact Nat.ass₁
  | cat₁ => exact Nat.cat₁ _ Nat.skip₁ h₂
  | cat₂ _ ih =>
    cases h₂ with
    | cat₁ _ hc hd =>
      exact Nat.cat₁ _ (ih hc) hd
  | ife₁ hb => exact Nat.ife₁ hb h₂
  | ife₂ hb => exact Nat.ife₂ hb h₂
  | wle₁ => rw [Nat.wle_unfold]; exact h₂

theorem ℂ.τ_imp_ε (h: cs ⇒* (skip, t)): cs ⟹ t :=
  by induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Nat.skip₁
  | head cs cs' ht => cases cs' <;> exact ε_imp_γ_imp_ε cs ht

theorem ℂ.τ_iff_ε: cs ⇒* (skip, t) ↔ cs ⟹ t := ⟨τ_imp_ε, ε_imp_τ⟩
