import Imp.Natural
import Imp.Structural


theorem ℂ.τ_imp_ε (h: τ c s skip s₁): ε c s s₁ :=
  by {
    revert s s₁
    induction c with
    | skip => {
      intro s s₁ h
      cases h
      constructor
      rename_i h₁ h₂
      cases h₁
    }
    | cat a b iha ihb => {
      intro s s₁ h
      have hh := τ.catex h
      cases hh
      rename_i w hh
      cases hh
      apply ε.cat₁
      . apply iha
        assumption
      . apply ihb
        assumption
    }
    | ass x a => {
      intro s s₁ h
      cases h
      rename_i h₁ h₂
      cases h₁
      cases h₂
      . constructor
      . rename_i h₁ h₂
        cases h₁
    }
    | ife b c d ihc ihd => {
      intro s s₁ h
      rw [ε.ife_ext]
      cases h
      rename_i h₁ h₂
      cases h₁
      cases hb: b.ρ s <;> (rw [hb] at h₂; simp at *)
      . apply ihd; assumption
      . apply ihc; assumption
    }
    | wle b c ih =>
      intro s s₁ h
      rw [ε.wle_unfold, ε.ife_ext]
      cases h
      rename_i h₁ h₂
      cases h₁
      cases hb: b.ρ s <;> (rw [hb] at h₂; simp at *)
      . cases h₂; constructor; rename_i h₁ h₂; cases h₁
      . {
        sorry
      }
  }

theorem ℂ.ε_imp_τ (h: ε c s s₁): τ c s skip s₁ :=
  by {
    induction h with
    | skip₁ => constructor
    | ass₁ => apply τ.self; constructor
    | cat₁ _ _ ihc ihd  => apply τ.cat _ ihc ihd
    | ife₁ hb _ ih =>
      rename_i c _  s _ _
      apply τ.step
      . apply γ.ife₁
      . rw [hb]
        assumption
    | ife₂ hb _ ih =>
      rename_i c d s _ _
      apply τ.step
      . apply γ.ife₁
      . rw [hb]
        assumption
    | wle₁ hb _ _ ihc ihw => {
      rename_i b c _ d s _ _
      apply τ.step
      . apply γ.wle₁
      . rw [hb]
        simp
        apply τ.cat _ ihc ihw
    }
    | wle₂ => {
      rename_i b c s hb
      apply τ.step
      . apply γ.wle₁
      . rw [hb]
        constructor
    }
  }

theorem  ℂ.ε_iff_τ: ε c s s₁ ↔ τ c s skip s₁ := by
  constructor
  . apply ε_imp_τ
  . apply τ_imp_ε

-- theorem ℂ.ε_iff_ρ : ε c s s₁ ↔ s₁ ∈ ρ c s :=
--   by
--     constructor
--     . {
--       intro h
--       induction h with
--       | skip => simp
--       | ass => simp
--       | cat s₂ _ _ ih₁ ih₂ => simp; exists s₂
--       | ife_tt hb _ ih =>
--         unfold ρ
--         rw [hb]
--         assumption
--       | ife_ff hb _ ih =>
--         unfold ρ
--         rw [hb]
--         assumption
--       | wle_tt s₂ hb _ _ ih₁ ih₂ =>
--         rw [wle_unfoldd]
--         unfold ρ
--         rw [hb]
--         simp
--         exists s₂
--       | wle_ff hb =>
--         rw [wle_unfoldd]
--         unfold ρ
--         rw [hb]
--         simp
--     }
--     . {
--       intro h
--       revert s s₁
--       induction c with
--       | skip => simp; intro _; constructor
--       | ass => simp; intro _; constructor
--       | cat c₁ c₂ ih₁ ih₂ =>
--         intro s s₁ h
--         simp at h
--         cases h with | intro s₂ hh =>
--           constructor
--           . apply ih₁; apply hh.left
--           . apply ih₂; apply hh.right

--       | ife b c₁ c₂ ih₁ ih₂ =>
--         intro s s₁ h
--         cases hh: 𝔹.ρ b s
--         . apply ℂ.ε.ife_ff
--           . assumption
--           . unfold ρ at h; rw [hh] at h; simp at h; apply ih₂; assumption
--         . apply ℂ.ε.ife_tt
--           . assumption
--           . unfold ρ at h; rw [hh] at h; simp at h; apply ih₁; assumption

--       | wle b c ih => {
--         intro s s₁ h
--         cases hb: 𝔹.ρ b s
--         . rw [ℂ.wle_unfoldd] at h
--           unfold ρ at h
--           rw [hb] at h
--           simp at h
--           rw [h]
--           apply ℂ.ε.wle_ff
--           assumption
--         . {
--           rw [ℂ.wle_unfold, ℂ.ife_unfold_ext]

--           unfold ρ at h
--           rw [hb] at h
--           simp at h
--           cases h
--           rename_i s₂ h

--         }
--       }
--     }
