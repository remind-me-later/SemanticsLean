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

-- WTF
noncomputable def ωSup (c: OmegaCompletePartialOrder.Chain (𝕊 →. 𝕊)) : (𝕊 →. 𝕊) :=
  fun s => if h: ∃s₁, ∃ f ∈ c, f s = Part.some s₁ then Part.some (Classical.choose h) else Part.none

noncomputable instance: OmegaCompletePartialOrder (𝕊 →. 𝕊) where
  ωSup := ωSup
  le_ωSup := by {
    intro c i s s₁ h
    unfold ωSup

    sorry
  }
  ωSup_le := by sorry

instance: LawfulFix (𝕊 →. 𝕊) where
  fix := Part.fix
  fix_eq := sorry

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

@[simp] def ℂ.ρ (c: ℂ): 𝕊 →. 𝕊 := fun s =>
  match c with
  | skip   => s
  | x ≔ₛ a => 𝕊.update s x (𝔸.ρ a s)
  | c₁;ₛc₂ => ρ c₁ s >>= ρ c₂
  | ife b c₁ c₂ => ite (𝔹.ρ b s) (ρ c₁ s) (ρ c₂ s)
  | wle b c => Fix.fix (Γ (𝔹.ρ b s) (ρ c)) s

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

theorem ℂ.ε_iff_ρ : ε c s s₁ ↔ ρ c s = s₁ :=
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
        simp
      | ite_tt hb _ ih =>
        simp
        rw [hb, ih]
        simp
      | ite_ff hb _ ih =>
        simp
        rw [hb, ih]
        simp
      | while_tt _ hb _ _ ih₁ ih₂ =>
        simp at *
        rw [hb, ←ih₂]
        unfold Γ
        simp
        sorry
      | while_ff hb =>
        simp
        rw [hb]
        unfold Γ
        simp
        unfold Fix.fix
        unfold LawfulFix.toFix
        unfold instLawfulFixPFun𝕊InstOmegaCompletePartialOrderPFun𝕊
        simp
        unfold Part.fix
        simp




        sorry

    }
    . {
      intro h
      simp at h
      -- induction c
      -- . simp at h; rw [h]; constructor
      -- . simp at h; rw [←h]; constructor
      sorry
    }
