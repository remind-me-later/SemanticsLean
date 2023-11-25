import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

import Mathlib.Logic.Relation

@[reducible]
inductive ℂ.Step: ℂ × 𝕊 → ℂ × 𝕊 → Prop
  | ass₁:
    Step (x ≔ a, s) (skip, s⟦x↦a↓s⟧)

  | cat₁:
    Step (skip;;c, s) (c, s)

  | cat₂ (h: Step (c, s) (e, t)):
    Step (c;;d, s) (e;;d, t)

  | ife₁ (hb: b↓s):
    Step (ife b c d, s) (c, s)

  | ife₂ {b: 𝔹} (hb: b↓s = false):
    Step (ife b c d, s) (d, s)

  | wle₁:
    Step (wle b c, s) (ife b (c;;wle b c) skip, s)

infix:110 " ⇒ " => ℂ.Step

example:
  (⦃x ≔ 2; while 0 ≤ x {x≔x-1}⦄, ⟦⟧) ⇒
      (⦃skip; while 0 ≤ x {x≔x-1}⦄, ⟦"x"↦2⟧) := ℂ.Step.cat₂ ℂ.Step.ass₁

infix:110 " ⇒* " => Relation.ReflTransGen ℂ.Step

example:
  (⦃ x ≔ 2; while 0 ≤ x {x≔x-1}⦄, ⟦⟧) ⇒*
      (⦃while 0 ≤ x {x≔x-1}⦄, (⟦"x"↦2⟧)) :=
  by
    apply Relation.ReflTransGen.head (ℂ.Step.cat₂ ℂ.Step.ass₁)
    apply Relation.ReflTransGen.head (ℂ.Step.cat₁)
    exact Relation.ReflTransGen.refl

theorem ℂ.Star.cat_skip_cat
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (skip;;c₂, s₁) :=
  Relation.ReflTransGen.lift (λ x ↦ (Prod.fst x;;c₂, Prod.snd x)) (λ _ _ h => Step.cat₂ h) h

theorem ℂ.Star.cat
  s₁
  (h₁: (c₁, s) ⇒* (skip, s₁))
  (h₂: (c₂, s₁) ⇒* (skip, s₂)):
  (c₁;;c₂, s) ⇒* (skip, s₂) :=
  by
  apply Relation.ReflTransGen.trans (cat_skip_cat h₁)
  apply Relation.ReflTransGen.trans _ h₂
  exact Relation.ReflTransGen.single Step.cat₁

theorem ℂ.Star.cat_no_influence
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (c₂, s₁) :=
  by
  apply Relation.ReflTransGen.trans (cat_skip_cat h)
  exact Relation.ReflTransGen.single (Step.cat₁)

@[simp] theorem ℂ.Step.cat_iff:
  (c₁;;c₂, s) ⇒ et ↔
  (∃e t, (c₁, s) ⇒ (e, t) ∧ et = (e;;c₂, t))
  ∨ (c₁ = skip ∧ et = (c₂, s)) :=
  by {
    constructor <;> intro h
    . {
      cases h with
      | cat₁ => exact Or.inr (And.intro rfl rfl)
      | cat₂ h =>
        rename_i e t
        apply Or.inl
        exists e, t
    }
    . {
      cases h <;> rename_i h <;> cases h
      . {
        rename_i e h
        cases h
        rename_i t h
        cases h
        rename_i left right
        cases right
        constructor
        assumption
      }
      . {
        rename_i left right
        cases left
        cases right
        constructor
      }
    }
  }

@[simp] lemma ℂ.Step.ite_iff:
  (ife b c d, s) ⇒ ss ↔
  (b↓s ∧ ss = (c, s)) ∨ (b↓s = false ∧ ss = (d, s)) :=
  by
  constructor <;> intro h
  . cases h <;> rename_i hb
    . exact Or.inl (And.intro hb rfl)
    . exact Or.inr (And.intro hb rfl)
  . cases h <;> rename_i h <;> cases h <;> rename_i left right <;> cases right
    . apply Step.ife₁ left
    . apply Step.ife₂ left
