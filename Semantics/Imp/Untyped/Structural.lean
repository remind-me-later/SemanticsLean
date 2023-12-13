import Semantics.Imp.Untyped.Bexp

import Mathlib.Logic.Relation

namespace Com
namespace Structural

@[reducible]
inductive step: Com × State → Com × State → Prop where
  | ass:
    step (ass x a, s) (skip, s⟪x ≔ a⇓s⟫)

  | cat₁:
    step (skip;;c, s) (c, s)

  | cat₂ (h: step (c, s) (e, t)):
    step (c;;d, s) (e;;d, t)

  | cond:
    step (cond b c d, s) (bif b⇓s then c else d, s)

  | loop:
    step (loop b c, s) (bif b⇓s then c;;loop b c else skip, s)

infix:110 " ⇒ " => step

theorem step.demo₁:
  (⦃x = 0; while x <= 2 {x = x + 1}⦄, σ₀) ⇒
      (⦃skip; while x <= 2 {x = x + 1}⦄, σ₀⟪"x" ≔ 0⟫) := cat₂ ass

@[simp] theorem cat_iff:
  (c₁;;c₂, s) ⇒ et ↔
  (∃e t, (c₁, s) ⇒ (e, t) ∧ et = (e;;c₂, t))
  ∨ (c₁ = skip ∧ et = (c₂, s)) := by
  constructor <;> intro h
  . cases h with
    | cat₁ => exact Or.inr ⟨rfl, rfl⟩
    | cat₂ h => exact Or.inl ⟨_, ⟨_, ⟨h, rfl⟩⟩⟩
  . cases h with
    | inl h =>
      cases h with | intro e h =>
        cases h with | intro t h =>
          exact h.right ▸ step.cat₂ h.1
    | inr h =>
      cases h with | intro h₁ h₂ =>
        exact h₁ ▸ h₂ ▸ step.cat₁

@[simp] lemma cond_iff:
  (cond b c d, s) ⇒ ss ↔
  (b⇓s ∧ ss = (c, s)) ∨ (b⇓s = false ∧ ss = (d, s)) := by
  constructor <;> intro h
  . cases hb: b⇓s <;> cases h
    . exact Or.inr ⟨rfl, hb ▸ rfl⟩
    . exact Or.inl ⟨rfl, hb ▸ rfl⟩
  . have hss: ss = (bif b⇓s then c else d, s) := by
      cases hb: b⇓s <;> rw [hb] at h <;> simp at * <;> assumption
    exact hss ▸ step.cond

@[simp] lemma cond_false {b: Bexp} (hb: b⇓s = false):
  (cond b c d, s) ⇒ ss ↔ (ss = (d, s)) :=
  by rw [cond_iff, hb]; simp

infix:110 " ⇒* " => Relation.ReflTransGen step

theorem star.demo₂:
  (⦃x = 2; while 0 <= x {x = x + 1}⦄, σ₀) ⇒*
      (⦃while 0 <= x {x = x + 1}⦄, σ₀⟪"x" ≔ 2⟫) :=
  Relation.ReflTransGen.head (step.cat₂ step.ass) (Relation.ReflTransGen.head step.cat₁ Relation.ReflTransGen.refl)

theorem star.cat_skip_cat
  (h: (c, s) ⇒* (skip, t)):
  (c;;d, s) ⇒* (skip;;d, t) :=
  Relation.ReflTransGen.lift (λ (x: Com × State) ↦ (x.1;;d, x.2)) (λ _ _ h => step.cat₂ h) h

theorem star.cat
  (h₁: (c₁, s) ⇒* (skip, s₁))
  (h₂: (c₂, s₁) ⇒* (skip, s₂)):
  (c₁;;c₂, s) ⇒* (skip, s₂) :=
  Relation.ReflTransGen.trans (cat_skip_cat h₁) (Relation.ReflTransGen.trans (Relation.ReflTransGen.single step.cat₁) h₂)

theorem star.cat_no_influence
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (c₂, s₁) :=
  Relation.ReflTransGen.trans (cat_skip_cat h) (Relation.ReflTransGen.single step.cat₁)

end Structural
end Com
