import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

import Std.Data.List.Basic
import Mathlib.Data.List.Chain

@[simp, reducible] def ℂ.γ (c: ℂ) (s: 𝕊): (Option ℂ) × 𝕊 :=
  match c with
  | skip        => (none, s)
  | x ≔ₛ a      => (skip, s⟦x ↦ (𝔸.ρ a s)⟧)
  | c₁;;c₂      =>
    let (c₁', s₁) := c₁.γ s
    if let some c₁' := c₁' then (c₁';;c₂, s₁) else (c₂, s₁)
  | ife b c₁ c₂ => ite (𝔹.ρ b s) (c₁, s) (c₂, s)
  | wle b c     => (ife b (c;;wle b c) skip, s)

def ex_program := ⟪y ≔ 1; while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}⟫

def ℂ.γ.sequence (x: ℂ × 𝕊) (k: Nat): (Option ℂ) × 𝕊 :=
  if k > 0 then
    let (c, s) := (γ x.1 x.2)
    if let some c₁ := c then
      sequence (c₁, s) (k - 1)
    else (c, s)
  else (x.1, x.2)

@[simp] def ℂ.γ.deriv_k (p: ℂ × 𝕊) (p₁: ℂ × 𝕊) (k: Nat) :=
  sequence p k = (some p₁.1, p₁.2)

@[simp] def ℂ.γ.deriv_star (p: ℂ × 𝕊) (p₁: ℂ × 𝕊) :=
  ∃k, deriv_k p p₁ k

@[simp] def ℂ.γ.deriv_term (p: ℂ × 𝕊) :=
  ∃s, deriv_star p (ℂ.skip, s)

#simp ℂ.γ.sequence (ex_program, ⟦⟧) 10

example: ℂ.γ.deriv_term (ex_program, ⟦⟧) :=
  by
    simp
    exists ⟦"y" ↦ 1⟧⟦"y" ↦ 0⟧⟦"x" ↦ 1⟧
    exists 10

theorem ℂ.γ.cat_k_if_n_m (hcat: deriv_k (c₁;;c₂, s) (skip, s₂) k):
  ∃k₁ k₂,  deriv_k (c₁, s) (skip, s₁) k₁ → deriv_k (c₂, s₁) (skip, s₂) k₂ →
  k₁ + k₂ = k :=
  by {
    induction k with
    | zero => {
      exists 0
      exists 0
      intro _ _
      rfl
    }
    | succ n ih => {
      cases ih
    }
  }

theorem ℂ.γ.cat_no_influence (hcat: deriv_star (c₁, s) (ℂ.skip, s₁)):
  deriv_star (c₁;;c₂, s) (c₂, s₁) :=
  by {
    unfold deriv_star at *
    cases hcat
    rename_i k hcat
    exists k+1
    simp
    unfold deriv_k at hcat
    unfold sequence
    simp
    induction k
    . {
      unfold sequence at *
      simp at *
      cases hcat
      rename_i l r
      cases r
      cases l
      reduce
      rfl
    }
    . {
      sorry
    }
  }
