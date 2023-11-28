import Imp.Untyped.Bexp

import Mathlib.Logic.Relation

namespace Com

inductive Step: Config → Config → Prop where
  | ass₁:
    Step (ass x a, s) (skip, s⟪x ≔ a⇓s⟫)

  | cat₁:
    Step (skip;;c, s) (c, s)

  | cat₂ (h: Step (c, s) (e, t)):
    Step (c;;d, s) (e;;d, t)

  | cond₁:
    Step (cond b c d, s) (bif b⇓s then (c, s) else (d, s))

  | loop₁:
    Step (loop b c, s) (cond b (c;;loop b c) skip, s)

infix:110 " ⇒ " => Step

namespace Step

theorem Step.demo₁:
  (⦃x = 2; while 0 <= x {x = x - 1}⦄, ⟪⟫) ⇒
      (⦃skip; while 0 <= x {x = x - 1}⦄, ⟪⟫⟪"x"≔2⟫) := cat₂ ass₁

@[simp] theorem cat_iff:
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

@[simp] lemma cond_iff:
  (cond b c d, s) ⇒ ss ↔
  (b⇓s ∧ ss = (c, s)) ∨ (b⇓s = false ∧ ss = (d, s)) :=
  by
  constructor <;> intro h
  . cases hb: b⇓s <;> cases h
    . exact Or.inr ⟨rfl, hb ▸ rfl⟩
    . exact Or.inl ⟨rfl, hb ▸ rfl⟩
  . have hss: ss = bif b⇓s then (c,s) else (d,s) := by
      cases hb: b⇓s <;> rw [hb] at h <;> simp at * <;> assumption
    exact hss ▸ cond₁

@[simp] lemma cond_false {b: Bexp} (hb: b⇓s = false):
  (cond b c d, s) ⇒ ss ↔ (ss = (d, s)) :=
  by rw [cond_iff, hb]; simp

end Step

open Relation

namespace Star

alias head   := ReflTransGen.head
alias trans  := ReflTransGen.trans
alias refl   := ReflTransGen.refl
alias single := ReflTransGen.single
alias lift   := ReflTransGen.lift
alias head_induction_on := ReflTransGen.head_induction_on

infix:110 " ⇒* " => ReflTransGen Step

theorem demo₂:
  (⦃x = 2; while 0 <= x {x = x - 1}⦄, ⟪⟫) ⇒*
      (⦃while 0 <= x {x = x - 1}⦄, ⟪⟫⟪"x"≔2⟫) :=
  head (Step.cat₂ Step.ass₁) (head Step.cat₁ Star.refl)

theorem cat_skip_cat
  (h: (c, s) ⇒* (skip, t)):
  (c;;d, s) ⇒* (skip;;d, t) :=
  lift (λ (x: Config) ↦ (x.1;;d, x.2)) (λ _ _ h => Step.cat₂ h) h

theorem cat
  (h₁: (c₁, s) ⇒* (skip, s₁))
  (h₂: (c₂, s₁) ⇒* (skip, s₂)):
  (c₁;;c₂, s) ⇒* (skip, s₂) :=
  trans (cat_skip_cat h₁) (trans (single Step.cat₁) h₂)

theorem cat_no_influence
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (c₂, s₁) :=
  trans (cat_skip_cat h) (single Step.cat₁)

end Star
end Com
