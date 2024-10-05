import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com
namespace Structural

inductive step: Com × State → Com × State → Prop where
  | assₛ:
    step (ass₁ x a, s) (skip₁, s[x ← a s])

  | cat₀ₛ:
    step (skip₁++c, s) (c, s)

  | catₙₛ (h: step (c, s) (e, t)):
    step (c++d, s) (e++d, t)

  | ifₛ:
    step (if b then c else d end, s) (bif b s then c else d, s)

  | whileₛ:
    step (while b loop c end, s)
          (bif b s then c++while b loop c end else skip₁, s)

infixl:10 " ⇒ " => step

private example:
  (⦃x = 0; while x <= 2 loop x = x + 1 end⦄, s₀) ⇒
      (⦃skip; while x <= 2 loop x = x + 1 end⦄, s₀["x" ← 0]) :=
  step.catₙₛ step.assₛ

theorem cat_eq:
  ((c₁++c₂, s) ⇒ et)
    = ((∃e t, ((c₁, s) ⇒ (e, t)) ∧ et = (e++c₂, t))
      ∨ (c₁ = skip₁ ∧ et = (c₂, s))) :=
  propext {
    mp := λ h => match h with
      | step.cat₀ₛ => Or.inr ⟨rfl, rfl⟩
      | step.catₙₛ h => Or.inl ⟨_, _, h, rfl⟩,
    mpr := λ h => match h with
      | Or.inl ⟨_, _, h1, h2⟩ => h2 ▸ step.catₙₛ h1
      | Or.inr ⟨h1, h2⟩ => h1 ▸ h2 ▸ step.cat₀ₛ
  }

theorem cond_eq:
  ((if b then c else d end, s) ⇒ ss)
    = (b s ∧ ss = (c, s) ∨ b s = false ∧ ss = (d, s)) :=
  propext {
    mp := λ h => match hb: b s with
      | false => match h with | step.ifₛ => Or.inr ⟨rfl, hb ▸ rfl⟩
      | true => match h with | step.ifₛ => Or.inl ⟨rfl, hb ▸ rfl⟩,
    mpr := λ h =>
      let hss: ss = (bif b s then c else d, s) :=
        match hb: b s with
        | true => match hb ▸ h with | Or.inl h => h.2
        | false => match hb ▸ h with | Or.inr h => h.2
      hss ▸ step.ifₛ
  }

theorem cond_false {b: Bexp} (hb: b s = false):
  ((if b then c else d end, s) ⇒ ss) = (ss = (d, s)) :=
  propext {
    mp := λ h => match hb ▸ cond_eq ▸ h with
      | Or.inr ⟨_, h2⟩ => h2,
    mpr := λ h => cond_eq ▸ Or.inr ⟨hb, h⟩
  }

infixl:10 " ⇒* " => RTL step

theorem star.demo₂:
  (⦃x = 2; while 0 <= x loop x = x + 1 end⦄, s₀) ⇒*
      (⦃while 0 <= x loop x = x + 1 end⦄, s₀["x" ← 2]) :=
  RTL.head (step.catₙₛ step.assₛ) (RTL.head step.cat₀ₛ RTL.refl)

theorem star.cat_skip_cat
  (h: (c, s) ⇒* (skip, t)):
  (c++d, s) ⇒* (skip++d, t) :=
  RTL.lift (λ (x: Com × State) => (x.1++d, x.2)) (λ _ _ h => step.catₙₛ h) h

theorem star.cat
  (h1: (c₁, s) ⇒* (skip₁, s₁))
  (h2: (c₂, s₁) ⇒* (skip₁, s₂)):
  (c₁++c₂, s) ⇒* (skip₁, s₂) :=
  RTL.trans (cat_skip_cat h1) (RTL.trans (RTL.single step.cat₀ₛ) h2)

theorem star.cat_no_influence
  (h: (c₁, s) ⇒* (skip₁, s₁)):
  (c₁++c₂, s) ⇒* (c₂, s₁) :=
  RTL.trans (cat_skip_cat h) (RTL.single step.cat₀ₛ)

end Structural
end Com
