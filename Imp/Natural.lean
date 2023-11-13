import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

-- Semantics of commands.
inductive ℂ.ε: ℂ → 𝕊 → 𝕊 → Prop
  | skip_ε:
    ε skip s s

  | ass_ε:
    ε (x ≔ a) s (s⟦x↦a.ρ s⟧)

  | cat_ε t (hc: c.ε s t) (hd: d.ε t u):
    ε (c;;d) s u

  | ife_tt_ε (hb: b.ρ s) (hc: c.ε s t):
    ε (ife b c d) s t

  | ife_ff_ε (hb: b.ρ s = false) (hd: d.ε s t):
    ε (ife b c d) s t

  | wle_tt_ε u (hb: b.ρ s) (hc: c.ε s u) (hw: (wle b c).ε u t):
    ε (wle b c) s t

  | wle_ff_ε (hb: b.ρ s = false):
    ε (wle b c) s s

example: ⟪x ≔ 5⟫.ε ⟦⟧ ⟦"x"↦5⟧ := by constructor

example:
  ⟪x ≔ 2; if x ≤ 1 {y ≔ 3} else {z ≔ 4}⟫.ε
  ⟦⟧
  (⟦"x"↦2⟧⟦"z"↦4⟧) :=
  by
    constructor
    . constructor
    . apply ℂ.ε.ife_ff_ε
      . simp
      . constructor

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
  constructor <;> intro h
  . cases h with | cat_ε _ hc => cases hc; assumption
  . constructor
    . constructor
    . assumption

theorem ℂ.ε.skipr: (c;;skip) ≈ c := by
  intro _ _
  constructor <;> intro h
  . cases h with | cat_ε _ _ hd => cases hd; assumption
  . constructor
    . assumption
    . constructor

theorem ℂ.ε.ife_tt (h: b ≈ 𝔹.tt):
  ife b c d ≈ c := by
  intro _ _; constructor <;> intro h₁
  . cases h₁ with
    | ife_tt_ε => assumption
    | ife_ff_ε hb => rw [h] at hb; contradiction
  . apply ε.ife_tt_ε
    . apply h
    . assumption

theorem ℂ.ε.ife_ff (h: b ≈ 𝔹.ff):
  ife b c d ≈ d := by
  intro t _
  constructor <;> intro h₁
  . cases h₁ with
    | ife_ff_ε => assumption
    | ife_tt_ε hb => rw [h] at hb; contradiction
  . apply ε.ife_ff_ε
    . apply h
    . assumption

theorem ℂ.ε.wle_unfold:
  wle b c ≈ ife b (c;;wle b c) skip := by
  intro s t
  constructor <;> intro h
  . cases hb: b.ρ s
    . apply ife_ff_ε
      . assumption
      . cases h
        . rw [hb] at *; contradiction
        . constructor
    . apply ife_tt_ε
      . assumption
      . cases h
        . constructor <;> assumption
        . rw [hb] at *; contradiction
  . cases hb: b.ρ s
    . cases h
      . rw [hb] at *; contradiction
      . rename_i hd; cases hd; apply wle_ff_ε; assumption
    . cases h
      . rename_i hc; cases hc; constructor <;> assumption
      . rw [hb] at *; contradiction

theorem ℂ.ε.ife_ext: (ife b c d).ε s t ↔ cond (b.ρ s) (c.ε s t) (d.ε s t) := by
  constructor <;> intro h
  . cases hb: b.ρ s <;> simp
    . cases h
      . rw [hb] at *; contradiction
      . assumption
    . cases h
      . assumption
      . rw [hb] at *; contradiction
  . cases hb: b.ρ s <;> (rw [hb] at h; simp at h)
    . apply ife_ff_ε <;> assumption
    . apply ife_tt_ε <;> assumption

theorem ℂ.ε.wle_tt (heqb: b ≈ 𝔹.tt):
  ¬((wle b c).ε s t) := by
  intro h
  generalize heqw: wle b c = w at h
  induction h with
  | wle_tt_ε _ _ _ _ _ ih₂ =>
    simp at heqw
    apply ih₂
    rw [←heqw.left, ←heqw.right]
  | wle_ff_ε hb =>
    simp at heqw
    rw [←heqw.left, heqb] at hb
    contradiction
  | _ => contradiction

theorem ℂ.ε.determ (h₁: ε c s t) (h₂: ε c s u):
  t = u := by
  revert u
  induction h₁ with
  | cat_ε u _ _ ih₁ ih₂ =>
    intro _ h; apply ih₂; cases h with | cat_ε u' =>
      have hi: u = u' := by apply ih₁; assumption
      cases hi; assumption

  | ife_tt_ε hb _ ih =>
    intro _ h; apply ih; cases h
    . assumption
    . rw [hb] at *; contradiction

  | ife_ff_ε hb _ ih =>
    intro _ h; apply ih; cases h
    . rw [hb] at *; contradiction
    . assumption

  | wle_tt_ε u hb _ _ ih₁ ih =>
    intro _ h; apply ih; cases h with
    | wle_tt_ε s₃ =>
      have hi: u = s₃ := by apply ih₁; assumption
      cases hi; assumption
    | wle_ff_ε hb₁ => rw [hb] at hb₁; contradiction

  | wle_ff_ε hb =>
    intro _ h; cases h
    . rw [hb] at *; contradiction
    . rfl

  | _ => intro _ h; cases h; rfl
