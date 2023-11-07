import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

import Mathlib.Init.Order.Defs
import Mathlib.Order.SuccPred.Basic

-- Semantics of commands.
inductive ℂ.γ: (ℂ × 𝕊) → (ℂ × 𝕊) → Prop
  | ass:
    γ (x ≔ₛ a, s) (skip, 𝕊.update s x (𝔸.ρ a s))

  | cat (hc₁: γ (c₁, s) (c₁', s₁)):
    γ (c₁;ₛc₂, s) (c₁';ₛc₂, s₁)

  | cat_skip (hc₁: γ (c₁, s) (skip, s₁)):
    γ (c₁;ₛc₂, s) (c₂, s₁)

  | ife:
    γ (ife b c₁ c₂, s) (ite (𝔹.ρ b s) (c₁, s) (c₂, s))

  | wle:
    γ (wle b c, s) (ife b (c;ₛwle b c) skip, s)

def ex_program := ⟪y ≔ 1; while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}⟫

example: ℂ.γ (ex_program, ⟦⟧)
  (⟪while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}⟫, ⟦y ↦ 1⟧) :=
  by repeat constructor

@[simp] def eval_rel (a b: ℂ × 𝕊) := ℂ.γ a b

@[simp] instance: LT (ℂ × 𝕊) where lt := eval_rel

@[simp] def derivation_chain (p: ℂ × 𝕊) cc :=
  ∃s, List.Chain eval_rel p cc ∧ (List.last' cc = some (ℂ.skip, s))

example: ∃cc, derivation_chain (ex_program, ⟦⟧) cc :=
  by
    {
      simp
      exists [
        (⟪while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}⟫, ⟦y ↦ 1⟧),
        (⟪if ¬(x = 1) {y ≔ y * x; x ≔ x + 1; while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}} else {skip}⟫, ⟦y ↦ 1⟧),
        (⟪y ≔ y * x; x ≔ x + 1; while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}⟫, ⟦y ↦ 1⟧),
        (⟪x ≔ x + 1; while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}⟫, ⟦y ↦ 1, y ↦ 0⟧),
        (⟪while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}⟫, ⟦y ↦ 1, y ↦ 0, x ↦ 1⟧),
        (⟪if ¬(x = 1) {y ≔ y * x; x ≔ x + 1; while ¬(x = 1) {y ≔ y * x; x ≔ x + 1}} else {skip}⟫, ⟦y ↦ 1, y ↦ 0, x ↦ 1⟧),
        (⟪skip⟫, ⟦y ↦ 1, y ↦ 0, x ↦ 1⟧)
      ]
      simp
      repeat constructor
    }
