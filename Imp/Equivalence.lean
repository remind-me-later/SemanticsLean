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
      apply ε.cat_ε w
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
      cases h
      rename_i h₁ h₂
      cases h₁
      . {
        apply ε.ife_tt_ε
        . assumption
        . apply ihc
          assumption
      }
      . {
        apply ε.ife_ff_ε
        . assumption
        . apply ihd
          assumption
      }
    }
    | wle b c =>
      intro s s₁ h
      generalize hs: skip = ss at h
      generalize hw: wle b c = ww at h ⊢
      induction h <;> cases hs <;> cases hw
      simp at *
      rename_i h₁ h₂ ih
      cases h₂
      rw [ε.wle_unfold]
      apply ih
      sorry
  }

theorem ℂ.ε_imp_τ (h: ε c s s₁): τ c s skip s₁ :=
  by {
    induction h with
    | skip_ε => constructor
    | ass_ε => apply τ.self; constructor
    | cat_ε t _ _ ihc ihd  => apply τ.cat t ihc ihd
    | ife_tt_ε hb _ ih =>
      rename_i c _  s _ _
      apply τ.step c s
      . apply γ.ife_tt_γ hb
      . assumption
    | ife_ff_ε hb _ ih =>
      rename_i c d s _ _
      apply τ.step d s
      . apply γ.ife_ff_γ hb
      . assumption
    | wle_tt_ε w hb _ _ ihc ihw => {
      rename_i b c d s _ _
      apply τ.step (ife b (c;;wle b c) skip) s
      . apply γ.wle_γ
      . apply τ.step (c;;wle b c) s
        . apply γ.ife_tt_γ hb
        . apply τ.cat w ihc ihw
    }
    | wle_ff_ε => {
      rename_i b c s hb
      apply τ.step (ife b (c;;wle b c) skip) s
      . apply γ.wle_γ
      . apply τ.step skip s
        . apply γ.ife_ff_γ hb
        . constructor
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
