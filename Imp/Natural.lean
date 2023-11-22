import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

-- Semantics of commands.
inductive ℂ.ε: ℂ → 𝕊 → 𝕊 → Prop
  | skip₁:
    ε skip s s

  | ass₁:
    ε (x ≔ a) s (s⟦x↦a.ρ s⟧)

  | cat₁ (hc: c.ε s t) (hd: d.ε t u):
    ε (c;;d) s u

  | ife₁ (hb: b.ρ s) (hc: c.ε s t):
    ε (ife b c d) s t

  | ife₂ (hb: b.ρ s = false) (hd: d.ε s t):
    ε (ife b c d) s t

  | wle₁ (hb: b.ρ s) (hc: c.ε s u) (hw: (wle b c).ε u t):
    ε (wle b c) s t

  | wle₂ (hb: b.ρ s = false):
    ε (wle b c) s s

theorem ℂ.ε.demo₁: ⟪x ≔ 5⟫.ε ⟦⟧ ⟦"x"↦5⟧ := ass₁

theorem ℂ.ε.demo₂:
  ε ⟪x ≔ 2; if x ≤ 1 {y ≔ 3} else {z ≔ 4}⟫ ⟦⟧
  (⟦"x"↦2⟧⟦"z"↦4⟧) := cat₁ ass₁ (ife₂ rfl ass₁)

theorem ℂ.ε.skip_same: ε skip s s₁ ↔ s = s₁ :=
  ⟨by intro h; cases h; rfl, (· ▸ skip₁)⟩

instance ℂ.ε.equiv: Setoid ℂ where
  r c d := ∀ s t, ε c s t ↔ ε d s t
  iseqv := {
    refl := by simp
    symm := by {
      intro _ _ h _ _
      apply Iff.symm
      apply h
    }
    trans := by {
      intro _ _ _ h₁ h₂ x _
      specialize h₁ x
      specialize h₂ x
      rw [h₁, h₂]
      simp
    }
  }

theorem ℂ.ε.skipl: (skip;;c) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat₁ hc hd =>
    exact skip_same.mp hc ▸ hd
  . exact (cat₁ skip₁ ·)

theorem ℂ.ε.skipr: (c;;skip) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat₁ hc hd =>
    exact skip_same.mp hd ▸ hc
  . exact (cat₁ · skip₁)

theorem ℂ.ε.ife_tt (h: b ≈ 𝔹.tt): ife b c d ≈ c := by
  intro _ _; constructor <;> intro h₁
  . cases h₁ with
    | ife₁ => assumption
    | ife₂ hb => rw [h] at hb; contradiction
  . apply ε.ife₁ _ h₁
    . apply h

theorem ℂ.ε.ife_ff (h: b ≈ 𝔹.ff): ife b c d ≈ d := by
  intro _ _; constructor <;> intro h₁
  . cases h₁ with
    | ife₂ => assumption
    | ife₁ hb => rw [h] at hb; contradiction
  . apply ε.ife₂ _ h₁
    . apply h

theorem ℂ.ε.wle_unfold:
  wle b c ≈ ife b (c;;wle b c) skip := by
  intro s t
  constructor <;> intro h
  . cases hb: b.ρ s
    . apply ife₂ hb
      cases h
      . rw [hb] at *; contradiction
      . constructor
    . apply ife₁ hb
      cases h
      . constructor <;> assumption
      . rw [hb] at *; contradiction
  . cases hb: b.ρ s
    . cases h
      . rw [hb] at *; contradiction
      . rename_i hd; cases hd; apply wle₂; assumption
    . cases h
      . rename_i hc; cases hc; constructor <;> assumption
      . rw [hb] at *; contradiction

theorem ℂ.ε.ife_ext: (ife b c d).ε s t ↔ cond (b.ρ s) (c.ε s t) (d.ε s t) := by
  constructor <;> intro h <;> cases hb: b.ρ s <;> simp at *
  . cases h
    simp [hb] at *
    assumption
  . cases h
    assumption
    simp [hb] at *
  . rw [hb] at h
    exact ife₂ hb h
  . rw [hb] at h
    exact ife₁ hb h

theorem ℂ.ε.ife_ext': (ife b c d).ε s t ↔ ε (cond (b.ρ s) c d) s t := by
  constructor <;> intro h <;> cases hb: b.ρ s <;> simp at *
  . cases h
    simp [hb] at *
    assumption
  . cases h
    assumption
    simp [hb] at *
  . rw [hb] at h
    exact ife₂ hb h
  . rw [hb] at h
    exact ife₁ hb h

theorem ℂ.ε.wle_tt (heqb: b ≈ 𝔹.tt):
  ¬(ε (wle b c) s t) := by
  intro h
  generalize heqw: wle b c = w at h
  induction h with
  | wle₁ _ _ _ _ ih₂ => exact ih₂ heqw
  | wle₂ hb => cases heqw; rw [heqb] at hb; contradiction
  | _ => contradiction

theorem ℂ.ε.determ (h₁: ε c s t) (h₂: ε c s u): t = u :=
  by induction h₁ generalizing u with
  | cat₁ _ _ ih₁ ih₂ => cases h₂ with
    | cat₁ hc hd => exact ih₂ (ih₁ hc ▸ hd)

  | ife₁ hb _ ih => cases h₂ with
    | ife₁ _ hd   => exact ih hd
    | ife₂ hb₁ hd => simp [hb] at hb₁

  | ife₂ hb _ ih => cases h₂ with
    | ife₁ hb₁ hd => simp [hb] at hb₁
    | ife₂ _ hd   => exact ih hd

  | wle₁ hb _ _ ih₁ ih₂ => cases h₂ with
    | wle₁ _ hc hw => exact ih₂ (ih₁ hc ▸ hw)
    | wle₂ hb₁     => simp [hb] at hb₁

  | wle₂ hb => cases h₂ with
    | wle₁ hb₁ => simp [hb] at hb₁
    | wle₂     => rfl

  | _ => cases h₂; rfl
