
theorem ℂ.ε_iff_ρ : ε c s s₁ ↔ s₁ ∈ ρ c s :=
  by
    constructor
    . {
      intro h
      induction h with
      | skip => simp
      | ass => simp
      | cat s₂ _ _ ih₁ ih₂ => simp; exists s₂
      | ife_tt hb _ ih =>
        unfold ρ
        rw [hb]
        assumption
      | ife_ff hb _ ih =>
        unfold ρ
        rw [hb]
        assumption
      | wle_tt s₂ hb _ _ ih₁ ih₂ =>
        rw [wle_unfoldd]
        unfold ρ
        rw [hb]
        simp
        exists s₂
      | wle_ff hb =>
        rw [wle_unfoldd]
        unfold ρ
        rw [hb]
        simp
    }
    . {
      intro h
      revert s s₁
      induction c with
      | skip => simp; intro _; constructor
      | ass => simp; intro _; constructor
      | cat c₁ c₂ ih₁ ih₂ =>
        intro s s₁ h
        simp at h
        cases h with | intro s₂ hh =>
          constructor
          . apply ih₁; apply hh.left
          . apply ih₂; apply hh.right

      | ife b c₁ c₂ ih₁ ih₂ =>
        intro s s₁ h
        cases hh: 𝔹.ρ b s
        . apply ℂ.ε.ife_ff
          . assumption
          . unfold ρ at h; rw [hh] at h; simp at h; apply ih₂; assumption
        . apply ℂ.ε.ife_tt
          . assumption
          . unfold ρ at h; rw [hh] at h; simp at h; apply ih₁; assumption

      | wle b c ih => {
        intro s s₁ h
        cases hb: 𝔹.ρ b s
        . rw [ℂ.wle_unfoldd] at h
          unfold ρ at h
          rw [hb] at h
          simp at h
          rw [h]
          apply ℂ.ε.wle_ff
          assumption
        . {
          rw [ℂ.wle_unfold, ℂ.ife_unfold_ext]

          unfold ρ at h
          rw [hb] at h
          simp at h
          cases h
          rename_i s₂ h

        }
      }
    }
