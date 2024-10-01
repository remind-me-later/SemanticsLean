import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com
namespace Structural

inductive step: Com × State → Com × State → Prop where
  | ass:
    step (x = a, s) (skip, s⟪x ≔ a⇓s⟫)

  | cat_skip:
    step (skip;;c, s) (c, s)

  | cat_step (h: step (c, s) (e, t)):
    step (c;;d, s) (e;;d, t)

  | cond:
    step (if b then c else d end, s) (bif b⇓s then c else d, s)

  | loop:
    step (while b loop c end, s) (bif b⇓s then c;;while b loop c end else skip, s)

infix:110 " ⇒ " => step

private example:
  (⦃x = 0; while x <= 2 {x = x + 1}⦄, σ₀) ⇒
      (⦃skip; while x <= 2 {x = x + 1}⦄, σ₀⟪"x" ≔ 0⟫) := step.cat_step step.ass

theorem cat_iff:
  (c₁;;c₂, s) ⇒ et
    ↔ (∃e t, (c₁, s) ⇒ (e, t) ∧ et = (e;;c₂, t))
      ∨ (c₁ = skip ∧ et = (c₂, s)) := by
  constructor <;> intro h
  . cases h with
    | cat_skip => exact Or.inr ⟨rfl, rfl⟩
    | cat_step h => exact Or.inl ⟨_, ⟨_, ⟨h, rfl⟩⟩⟩
  . cases h with
    | inl h =>
      cases h with
      | intro e h =>
        cases h with
        | intro t h =>
          exact h.right ▸ step.cat_step h.1
    | inr h =>
      cases h with
      | intro h1 h2 =>
        exact h1 ▸ h2 ▸ step.cat_skip

theorem cond_iff:
  (if b then c else d end, s) ⇒ ss
    ↔ (b⇓s ∧ ss = (c, s)) ∨ (b⇓s = false ∧ ss = (d, s)) := by
  constructor <;> intro h
  . cases hb: b⇓s <;> cases h
    . exact Or.inr ⟨rfl, hb ▸ rfl⟩
    . exact Or.inl ⟨rfl, hb ▸ rfl⟩
  . have hss: ss = (bif b⇓s then c else d, s) := by
      cases hb: b⇓s <;> rw [hb] at h <;> simp at * <;> assumption
    exact hss ▸ step.cond

theorem cond_false {b: Bexp} (hb: b⇓s = false):
  (if b then c else d end, s) ⇒ ss ↔ (ss = (d, s)) :=
  by
    simp [cond_iff, hb]

infix:110 " ⇒* " => RTL step

theorem star.demo₂:
  (⦃x = 2; while 0 <= x {x = x + 1}⦄, σ₀) ⇒*
      (⦃while 0 <= x {x = x + 1}⦄, σ₀⟪"x" ≔ 2⟫) :=
  RTL.head (step.cat_step step.ass) (RTL.head step.cat_skip RTL.refl)

theorem star.cat_skip_cat
  (h: (c, s) ⇒* (skip, t)):
  (c;;d, s) ⇒* (skip;;d, t) :=
  RTL.lift (fun (x: Com × State) => (x.1;;d, x.2)) (fun _ _ h => step.cat_step h) h

theorem star.cat
  (h1: (c₁, s) ⇒* (skip, s₁))
  (h2: (c₂, s₁) ⇒* (skip, s₂)):
  (c₁;;c₂, s) ⇒* (skip, s₂) :=
  RTL.trans (cat_skip_cat h1) (RTL.trans (RTL.single step.cat_skip) h2)

theorem star.cat_no_influence
  (h: (c₁, s) ⇒* (skip, s₁)):
  (c₁;;c₂, s) ⇒* (c₂, s₁) :=
  RTL.trans (cat_skip_cat h) (RTL.single step.cat_skip)

end Structural
end Com
