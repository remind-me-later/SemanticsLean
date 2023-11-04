import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax
import Imp.BigStep

import Mathlib.Control.Fix
import Mathlib.Control.LawfulFix
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.PFun
import Mathlib.Data.Part

instance: PartialOrder (𝕊 →. 𝕊) where
  le a b := ∀s s₁, a s = s₁ → b s = s₁
  le_refl := by simp
  le_trans := by {
    intro a b c h₁ h₂ s s₁ h
    simp at *
    specialize h₁ s
    specialize h₂ s
    rw [h₂, h₁]
    assumption
  }
  le_antisymm := by {
    intro a b h₁ h₂
    simp at *
    apply funext
    intro s
    specialize h₁ s
    specialize h₂ s
    rw [h₂, h₁]
  }

instance (c: OmegaCompletePartialOrder.Chain (𝕊 →. 𝕊)): Decidable (∃ s₁ f, f ∈ c ∧ f s = Part.some s₁) := sorry

noncomputable def ρ_ωSup (c: OmegaCompletePartialOrder.Chain (𝕊 →. 𝕊)) : (𝕊 →. 𝕊) :=
  fun s => if h: ∃s₁: 𝕊, ∃ f ∈ c, f s = Part.some s₁ then Part.some (Classical.choose h) else Part.none

theorem ρ_ωSup_eq_some {c : OmegaCompletePartialOrder.Chain (𝕊 →. 𝕊)} (h : ∃ f ∈ c, f s = Part.some s₁) : ρ_ωSup c = f := sorry

noncomputable instance: OmegaCompletePartialOrder (𝕊 →. 𝕊) where
  ωSup := ρ_ωSup
  le_ωSup := by {
    intro c i s s₁ h
    unfold ρ_ωSup
    sorry
  }
  ωSup_le := by {
    intro c x h s s₁ h₁
    sorry
  }

def Γ (b: Bool) (f: 𝕊 →. 𝕊): (𝕊 →. 𝕊) →𝒄 (𝕊 →. 𝕊) :=
  {
    toFun := fun g s => ite b (f s >>= g) s
    monotone' := by sorry
    cont := by {
      unfold OmegaCompletePartialOrder.Continuous
      simp
      sorry
    }
  }

@[simp, reducible] def ℂ.ρ (c: ℂ) (s: 𝕊): Part 𝕊 :=
  match c with
  | skip   => s
  | x ≔ₛ a => 𝕊.update s x (𝔸.ρ a s)
  | c₁;ₛc₂ => ρ c₁ s >>= ρ c₂
  | ife b c₁ c₂ => ite (𝔹.ρ b s) (ρ c₁ s) (ρ c₂ s)
  | wle b c => Part.fix (Γ (𝔹.ρ b s) (ρ c)) s

#simp ℂ.ρ ⟪x ≔ 2; if x ≤ 1 {y ≔ 3} else {z ≔ 4}⟫ ⟦⟧

def ℂ.ρ_eq c₁ c₂ := ∀ s, ρ c₁ s = ρ c₂ s

instance: Setoid ℂ where
  r := ℂ.ρ_eq
  iseqv := {
    refl := by {
      unfold ℂ.ρ_eq
      simp
    }
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

theorem ℂ.skipld: (skip;ₛc) ≈ c := by intro s; simp

theorem ℂ.skiprd: (c;ₛskip) ≈ c := by intro s; simp

theorem ℂ.if_trued (hb: b ≈ 𝔹.tt):
  ife b c₁ c₂ ≈ c₁ :=
  by
    intro s
    simp
    rw [hb]
    simp

theorem ℂ.if_falsed (hb: b ≈ 𝔹.ff):
  ife b c₁ c₂ ≈ c₂ :=
  by
    intro s
    simp
    rw [hb]
    simp

theorem ℂ.ε_iff_ρ : ε c s s₁ ↔ ρ c s = Part.some s₁ :=
  by
    constructor
    . {
      intro h
      induction h with
      | skip => simp
      | ass => simp
      | cat _ _ _ ih₁ ih₂ =>
        simp
        rw [ih₁]
        simp
        rw [ih₂]
      | ite_tt hb _ ih =>
        simp
        rw [hb, ih]
        simp
      | ite_ff hb _ ih =>
        simp
        rw [hb, ih]
        simp
      | wle_tt s₂ hb _ _ ih₁ ih₂ =>
        simp at *
        rw [hb]
        unfold Γ at *
        simp at *
        sorry

      | wle_ff hb =>
        simp
        rw [hb, Part.fix_def]
        . unfold Part.Fix.approx; rfl
        . exists 1
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
        have s₂: 𝕊 := default
        have hh: (ρ c₁ s) = Part.some s₂ := by {
          unfold Part.bind at h

        }
        rw [hh] at h
        simp at h
        constructor
        . apply ih₁
          assumption
        . apply ih₂
          assumption

      | ife b c₁ c₂ ih₁ ih₂ => {
        intro s s₁ h
        cases hh: 𝔹.ρ b s
        . {
          apply ℂ.ε.ite_ff
          . assumption
          . simp at h; rw [hh] at h; simp at h; apply ih₂; assumption
        }
        . {
          apply ℂ.ε.ite_tt
          . assumption
          . simp at h; rw [hh] at h; simp at h; apply ih₁; assumption
        }
      }

      | wle b c ih => {
        intro s s₁ h
        cases hh: 𝔹.ρ b s
        . {
          simp at h
          rw [hh] at h
          unfold Γ at h
          simp at h
          rw [Part.fix_def] at h
          unfold Part.Fix.approx at h
          . {
            simp at h
            cases h
            apply ℂ.ε.wle_ff
            assumption
          }
          . {
            exists 1
          }
        }
        . {
          sorry
        }
      }
    }
