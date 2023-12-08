import Semantics.Imp.Untyped.Bexp

import Mathlib.Logic.Relation

namespace Com
namespace Structural

@[reducible]
inductive Step: Com × State → Com × State → Prop where
  | ass₁:
    Step (ass x a, s) (skip, s⟪x ≔ a⇓s⟫)

  | cat₁:
    Step (skip;;c, s) (c, s)

  | cat₂ (h: Step (c, s) (e, t)):
    Step (c;;d, s) (e;;d, t)

  | cond₁:
    Step (cond b c d, s) (bif b⇓s then c else d, s)

  | loop₁:
    Step (loop b c, s) (bif b⇓s then c;;loop b c else skip, s)

infix:110 " ⇒ " => Step

theorem Step.demo₁:
  (⦃x = 2; while 0 <= x {x = x - 1}⦄, ⟪⟫) ⇒
      (⦃skip; while 0 <= x {x = x - 1}⦄, ⟪⟫⟪"x"≔2⟫) := cat₂ ass₁

@[simp] theorem Step.cat_iff:
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
          exact h.right ▸ Step.cat₂ h.1
    | inr h =>
      cases h with | intro h₁ h₂ =>
        exact h₁ ▸ h₂ ▸ Step.cat₁

@[simp] lemma Step.cond_iff:
  (cond b c d, s) ⇒ ss ↔
  (b⇓s ∧ ss = (c, s)) ∨ (b⇓s = false ∧ ss = (d, s)) := by
  constructor <;> intro h
  . cases hb: b⇓s <;> cases h
    . exact Or.inr ⟨rfl, hb ▸ rfl⟩
    . exact Or.inl ⟨rfl, hb ▸ rfl⟩
  . have hss: ss = (bif b⇓s then c else d, s) := by
      cases hb: b⇓s <;> rw [hb] at h <;> simp at * <;> assumption
    exact hss ▸ Step.cond₁

@[simp] lemma Step.cond_false {b: Bexp} (hb: b⇓s = false):
  (cond b c d, s) ⇒ ss ↔ (ss = (d, s)) :=
  by rw [cond_iff, hb]; simp

infix:110 " ⇒* " => Relation.ReflTransGen Step

theorem StarStep.demo₂:
  (⦃x = 2; while 0 <= x {x = x - 1}⦄, ⟪⟫) ⇒*
      (⦃while 0 <= x {x = x - 1}⦄, ⟪⟫⟪"x"≔2⟫) :=
  Relation.ReflTransGen.head (Step.cat₂ Step.ass₁) (Relation.ReflTransGen.head Step.cat₁ Relation.ReflTransGen.refl)

theorem StarStep.cat_skip_cat
  (h: (c, s) ⇒* (skip, t)):
  (c;;d, s) ⇒* (skip;;d, t) :=
  Relation.ReflTransGen.lift (λ (x: Com × State) ↦ (x.1;;d, x.2)) (λ _ _ h => Step.cat₂ h) h

theorem StarStep.cat
  (h₁: (c₁, s) ⇒* (skip, s₁))
  (h₂: (c₂, s₁) ⇒* (skip, s₂)):
  (c₁;;c₂, s) ⇒* (skip, s₂) :=
  Relation.ReflTransGen.trans (cat_skip_cat h₁) (Relation.ReflTransGen.trans (Relation.ReflTransGen.single Step.cat₁) h₂)

theorem StarStep.cat_no_influence
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (c₂, s₁) :=
  Relation.ReflTransGen.trans (cat_skip_cat h) (Relation.ReflTransGen.single Step.cat₁)

end Structural
end Com
