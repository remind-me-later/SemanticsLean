import Imp.Natural
import Imp.Structural


theorem ℂ.γ_imp_ε (h: γ (c, s, k) (skip, s₁, k₁)): ε c s s₁ :=
  by {
    induction c with
    | skip => {
      cases h
      repeat constructor
    }
    | cat a b iha ihb => {
      cases h
      constructor
      . apply iha; assumption
      . constructor
    }
    | ass x a => {
      cases h
      constructor
    }
    | ife b c d ihc ihd => {
      cases h
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
      cases h
      rename_i h
      cases h
      . {
        rename_i ih hb h
        cases h
      }
      . {
        rename_i ih hb h
        cases h
        apply ε.wle_ff_ε; assumption
      }
  }

theorem ℂ.ε_imp_γ (h: ε c s s₁): ∃k, γ (c, s, k) (skip, s₁, 0) :=
  by {
    induction h with
    | skip_ε => exists 0; constructor
    | ass_ε => exists 1; constructor
    | cat_ε t _ _ ihc ihd  =>
      cases ihc
      rename_i kc ihc
      cases ihd
      rename_i kd ihd
      exists kc + kd
      apply γ.cat_k_iff
      . assumption
      . assumption
    | ife_tt_ε hb _ ih =>
      cases ih
      rename_i k ih
      exists k
      apply γ.ife_tt_γ <;> assumption
    | ife_ff_ε hb _ ih =>
      cases ih
      rename_i k ih
      exists k
      apply γ.ife_ff_γ <;> assumption
    | wle_tt_ε w hb _ _ ihc ihw => {
      cases ihc
      rename_i k ihc
      cases ihw
      rename_i n ihw
      exists k + n
      constructor
      apply γ.ife_tt_γ
      . assumption
      . apply γ.cat_k_iff
        . assumption
        . assumption
    }
    | wle_ff_ε => {
      exists 0
      constructor
      apply γ.ife_ff_γ
      . assumption
      . constructor
    }
  }


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
