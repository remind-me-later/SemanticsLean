import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

inductive ℂ.γ: ℂ × 𝕊 × Nat → ℂ × 𝕊 × Nat → Prop
  | zero_γ:
    γ (c, s, 0) (c, s, 0)

  | ass_γ:
    γ (x ≔ a, s, n + 1) (skip, s⟦x↦a.ρ s⟧, n)

  | cat_γ (h: γ (c₁, s, n) (c₁', s₁, k)):
    γ (c₁;;c₂, s, n) (c₁';;c₂, s₁, k)

  | cat_skip_γ (h: γ (c₁, s, n) (skip, s₁, k)):
    γ (c₁;;c₂, s, n) (c₂, s₁, k)

  | ife_tt_γ (hb: b.ρ s) (h: γ (c₁, s, n) (c₁', s₁, k)):
    γ (ife b c₁ c₂, s, n) (c₁', s₁, k)

  | ife_ff_γ (hb: b.ρ s = false) (h: γ (c₂, s, n) (c₂', s₁, k)):
    γ (ife b c₁ c₂, s, n) (c₂', s₁, k)

  | wle_γ (h: γ (ife b (c;;wle b c) skip, s, n) (c₁, s₁, k)):
    γ (wle b c, s, n) (c₁, s₁, k)

example:
  ℂ.γ (⟪x ≔ 2; while 0 ≤ x {x≔x-1}⟫, ⟦⟧, 1)
      (⟪while 0 ≤ x {x≔x-1}⟫, ⟦"x"↦2⟧, 0) :=
  by repeat constructor

theorem ℂ.γ.skip_skip: γ (skip;;skip, s, k) (skip, s, 0) ↔ γ (skip, s, k₁) (skip, s, 0)
     :=
  by {
    sorry
  }

theorem ℂ.γ.cat_k_iff
  (h₁: γ (c₁, s, n) (skip, s₁, 0))
  (h₂: γ (c₂, s₁, m) (skip, s₂, 0)):
  γ (c₁;;c₂, s, n + m) (skip, s₂, 0)
     :=
  by {
    sorry

  }

theorem ℂ.γ.cat_k_iff_n_m (h: γ (c₁;;c₂, s, k) (skip, s₂, 0)):
    ∃ n m s₁, γ (c₁, s, n) (skip, s₁, 0)
    ∧ γ (c₂, s₁, m) (skip, s₂, 0)
    ∧ n + m = k :=
  by {
    cases h
    rename_i h
    exists k
    exists 0
    exists s₂
    constructor
    . assumption
    . constructor
      . constructor
      . simp
  }

theorem ℂ.γ.cat_no_influence
  (hcat: γ (c₁, s, k) (skip, s₁, 0)):
  γ (c₁;;c₂, s, k) (c₂, s₁, 0) :=
  by constructor; assumption
