import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

inductive ℂ.γ: ℂ × 𝕊 × Nat → ℂ × 𝕊 × Nat → Prop
  | skip_γ:
    γ (skip, s, n) (skip, s, n - 1)

  | ass_γ:
    γ (x ≔ₛ a, s, n) (skip, s⟦x↦a.ρ s⟧, n - 1)

  | cat_γ (h: γ (c₁, s, n) (c₁', s₁, k)):
    γ (c₁;;c₂, s, n) (c₁';;c₂, s₁, k)

  | cat_skip_γ (h: γ (c₁, s, n) (skip, s₁, k)):
    γ (c₁;;c₂, s, n) (c₂, s₁, k)

  | ife_γ:
    γ (ife b c₁ c₂, s, n) (cond (𝔹.ρ b s) (c₁, s, n - 1) (c₂, s, n - 1))

  | wle_γ:
    γ (wle b c, s, n) (ife b (c;;wle b c) skip, s, n - 1)

example: ℂ.γ (⟪x ≔ 2; while 0 ≤ x {x≔x-1}⟫, ⟦⟧, 1) (⟪while 0 ≤ x {x≔x-1}⟫, ⟦"x"↦2⟧, 0) :=
  by repeat constructor

theorem ℂ.γ.cat_k_if_n_m
  (hcat: γ (c₁;;c₂, s, k) (skip, s₂, 0)):
  ∃k₁ k₂ s₁,
    γ (c₁, s, k₁) (skip, s₁, 0)
    ∧ γ (c₂, s₁, k₂) (skip, s₂, 0)
    ∧ k₁ + k₂ = k :=
  by {
    cases hcat
    rename_i h
    exists k
    exists 0
    exists s₂
    constructor
    . assumption
    . constructor
      . constructor
      . rfl
  }

theorem ℂ.γ.cat_no_influence (hcat: γ (c₁, s, k) (skip, s₁, 0)):
  γ (c₁;;c₂, s, k) (c₂, s₁, 0) :=
  by constructor; assumption
