import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

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

instance (c: OmegaCompletePartialOrder.Chain (𝕊 →. 𝕊)): Decidable (∃s₁, ∃ f ∈ c, s₁ ∈ f s) := sorry

noncomputable def ρ_ωSup (c: OmegaCompletePartialOrder.Chain (𝕊 →. 𝕊)) : (𝕊 →. 𝕊) :=
  fun s => if h: ∃s₁, ∃ f ∈ c, s₁ ∈ f s then Part.some (Classical.choose h) else Part.none

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

@[reducible] def ℂ.ρ (c: ℂ) (s: 𝕊): Part 𝕊 :=
  match c with
  | skip   => s
  | x ≔ₛ a => 𝕊.update s x (𝔸.ρ a s)
  | c₁;ₛc₂ => ρ c₁ s >>= ρ c₂
  | ife b c₁ c₂ => ite (𝔹.ρ b s) (ρ c₁ s) (ρ c₂ s)
  | wle b c => Part.fix (Γ (𝔹.ρ b s) (ρ c)) s

#simp  ℂ.ρ ⟪x ≔ 2; if x ≤ 1 {y ≔ 3} else {z ≔ 4}⟫ ⟦⟧

@[simp] def ℂ.ρ_eq c₁ c₂ := ∀ s, ρ c₁ s = ρ c₂ s

@[simp] instance: Setoid ℂ where
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

theorem ℂ.wle_unfoldd: wle b c ≈ ife b (c;ₛwle b c) skip := sorry

theorem ℂ.skipld: (skip;ₛc) ≈ c := by intro _; simp

theorem ℂ.skiprd: (c;ₛskip) ≈ c := by intro s; simp; sorry

theorem ℂ.if_trued (hb: b ≈ 𝔹.tt):
  ife b c₁ c₂ ≈ c₁ :=
  by
    intro _
    simp
    rw [hb]
    simp

theorem ℂ.if_falsed (hb: b ≈ 𝔹.ff):
  ife b c₁ c₂ ≈ c₂ :=
  by
    intro _
    simp
    rw [hb]
    simp
