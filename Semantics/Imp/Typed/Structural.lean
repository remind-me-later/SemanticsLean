import Semantics.Imp.Untyped.Bexp

import Mathlib.Logic.Relation

namespace Com
namespace Structural

@[reducible]
inductive Step: Com × State → Com × State → Prop where
  | ass (h: Aexp.Natural.Step a s n):
    Step (ass x a, s) (skip, s⟪x ≔ n⟫)

  | cat₁:
    Step (skip;;c, s) (c, s)

  | cat₂ (h: Step (c, s) (e, t)):
    Step (c;;d, s) (e;;d, t)

  | cond (h: Bexp.Natural.Step b s t):
    Step (cond b c d, s) (bif t then c else d, s)

  | loop (h: Bexp.Natural.Step b s t):
    Step (loop b c, s) (bif t then c;;loop b c else skip, s)

infix:110 " ⇒ " => Step

theorem Step.demo₁:
  (⦃x = 0; while x <= 2 {x = x + 1}⦄, ⟪⟫) ⇒
      (⦃skip; while x <= 2 {x = x + 1}⦄, ⟪⟫⟪"x"≔0⟫) := cat₂ (ass (by simp))

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
          exact h.right ▸ Step.cat₂ h.1
    | inr h =>
      cases h with | intro h₁ h₂ =>
        exact h₁ ▸ h₂ ▸ Step.cat₁

@[simp] lemma cond_iff:
  (cond b c d, s) ⇒ ss ↔
  (b.reduce s ∧ ss = (c, s)) ∨ (b.reduce s = false ∧ ss = (d, s)) := by
  constructor <;> intro h
  . cases hb: b.reduce s <;> cases h
    . sorry
    . sorry
  . have hss: ss = (bif b.reduce s then c else d, s) := by
      cases hb: b.reduce s <;> rw [hb] at h <;> simp at * <;> assumption
    sorry

@[simp] lemma cond_false {b: Bexp} (hb: b.reduce s = false):
  (cond b c d, s) ⇒ ss ↔ (ss = (d, s)) :=
  by rw [cond_iff, hb]; simp

infix:110 " ⇒* " => Relation.ReflTransGen Step

theorem Star.demo₂:
  (⦃x = 2; while 0 <= x {x = x + 1}⦄, ⟪⟫) ⇒*
      (⦃while 0 <= x {x = x + 1}⦄, ⟪⟫⟪"x"≔2⟫) :=
  Relation.ReflTransGen.head (Step.cat₂ (Step.ass (by simp))) (Relation.ReflTransGen.head Step.cat₁ Relation.ReflTransGen.refl)

theorem Star.cat_skip_cat
  (h: (c, s) ⇒* (skip, t)):
  (c;;d, s) ⇒* (skip;;d, t) :=
  Relation.ReflTransGen.lift (λ (x: Com × State) ↦ (x.1;;d, x.2)) (λ _ _ h => Step.cat₂ h) h

theorem Star.cat
  (h₁: (c₁, s) ⇒* (skip, s₁))
  (h₂: (c₂, s₁) ⇒* (skip, s₂)):
  (c₁;;c₂, s) ⇒* (skip, s₂) :=
  Relation.ReflTransGen.trans (cat_skip_cat h₁) (Relation.ReflTransGen.trans (Relation.ReflTransGen.single Step.cat₁) h₂)

theorem Star.cat_no_influence
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (c₂, s₁) :=
  Relation.ReflTransGen.trans (cat_skip_cat h) (Relation.ReflTransGen.single Step.cat₁)

end Structural
end Com
