import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

import Mathlib.Logic.Relation

inductive ℂ.Step: ℂ × 𝕊 → ℂ × 𝕊 → Prop
  | ass₁:
    Step (x ≔ a, s) (skip, s⟦x↦a↓s⟧)

  | cat₁:
    Step (skip;;c, s) (c, s)

  | cat₂ (h: Step (c, s) (e, t)):
    Step (c;;d, s) (e;;d, t)

  | ife₁:
    Step (ife b c d, s) (cond (b↓s) (c, s) (d, s))

  | wle₁:
    Step (wle b c, s) (ife b (c;;wle b c) skip, s)

infix:110 " ⇒ " => ℂ.Step

theorem ℂ.Step.demo₁:
  (⦃x ≔ 2; while 0 ≤ x {x≔x-1}⦄, ⟦⟧) ⇒
      (⦃skip; while 0 ≤ x {x≔x-1}⦄, ⟦"x"↦2⟧) := cat₂ ass₁

@[simp] theorem ℂ.Step.cat_iff:
  (c₁;;c₂, s) ⇒ et ↔
  (∃e t, (c₁, s) ⇒ (e, t) ∧ et = (e;;c₂, t))
  ∨ (c₁ = skip ∧ et = (c₂, s)) :=
  by
  constructor <;> intro h
  . cases h with
    | cat₁ => exact Or.inr ⟨rfl, rfl⟩
    | cat₂ h => exact Or.inl ⟨_, ⟨_, ⟨h, rfl⟩⟩⟩
  . cases h with
    | inl h =>
      cases h with | intro e h =>
        cases h with | intro t h =>
          exact h.right ▸ cat₂ h.left
    | inr h =>
      cases h with | intro h₁ h₂ =>
        exact h₁ ▸ h₂ ▸ Step.cat₁

@[simp] lemma ℂ.Step.ite_iff:
  (ife b c d, s) ⇒ ss ↔
  (b↓s ∧ ss = (c, s)) ∨ (b↓s = false ∧ ss = (d, s)) :=
  by
  constructor <;> intro h
  . cases hb: b↓s <;> cases h
    . exact Or.inr (And.intro rfl (hb ▸ rfl))
    . exact Or.inl (And.intro rfl (hb ▸ rfl))
  . have hss: ss = cond (b↓s) (c,s) (d,s) := by
      cases hb: b↓s <;> rw [hb] at h <;> simp at * <;> assumption
    exact hss ▸ ife₁

open Relation

infix:110 " ⇒* " => ReflTransGen ℂ.Step

theorem ℂ.Star.demo₂:
  (⦃ x ≔ 2; while 0 ≤ x {x≔x-1}⦄, ⟦⟧) ⇒*
      (⦃while 0 ≤ x {x≔x-1}⦄, (⟦"x"↦2⟧)) :=
  ReflTransGen.head (Step.cat₂ Step.ass₁) (ReflTransGen.head Step.cat₁ ReflTransGen.refl)

theorem ℂ.Star.cat_skip_cat
  (h: (c, s) ⇒* (skip, t)):
  (c;;d, s) ⇒* (skip;;d, t) :=
  ReflTransGen.lift (λ x ↦ (Prod.fst x;;d, Prod.snd x)) (λ _ _ h => Step.cat₂ h) h

theorem ℂ.Star.cat
  (h₁: (c₁, s) ⇒* (skip, s₁))
  (h₂: (c₂, s₁) ⇒* (skip, s₂)):
  (c₁;;c₂, s) ⇒* (skip, s₂) :=
  by
  apply ReflTransGen.trans (cat_skip_cat h₁)
  exact ReflTransGen.trans (ReflTransGen.single Step.cat₁) h₂

theorem ℂ.Star.cat_no_influence
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (c₂, s₁) :=
  ReflTransGen.trans (cat_skip_cat h) (ReflTransGen.single Step.cat₁)
