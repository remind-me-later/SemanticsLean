import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com
namespace Structural

inductive small_step: Config → Config → Prop where
  | assₛ:
    small_step (ass₁ v a, s) (skip₁, s[v ← a s])

  | cat₀ₛ:
    small_step (skip₁++c, s) (c, s)

  | catₙₛ (h: small_step (c₁, s₁) (c₂, s₂)):
    small_step (c₁++c₃, s₁) (c₂++c₃, s₂)

  | ifₛ:
    small_step (if b then c₁ else c₂ end, s) (bif b s then c₁ else c₂, s)

  | whileₛ:
    small_step (while b loop c end, s)
          (bif b s then c++while b loop c end else skip₁, s)

infixl:10 " =>ₛ " => small_step

private example:
  ([|x := 0; while x ≤ 2 loop x := x + 1 end|], s₀) =>ₛ
      ([|skip; while x ≤ 2 loop x := x + 1 end|], s₀["x" ← 0]) :=
  small_step.catₙₛ small_step.assₛ

theorem cat_eq:
  ((c₁++c₃, s₁) =>ₛ conf)
    = ((∃c₂ s₂, ((c₁, s₁) =>ₛ (c₂, s₂)) ∧ conf = (c₂++c₃, s₂))
      ∨ (c₁ = skip₁ ∧ conf = (c₃, s₁))) :=
  propext {
    mp := λ hmp ↦ match hmp with
      | small_step.cat₀ₛ => Or.inr ⟨rfl, rfl⟩
      | small_step.catₙₛ h => Or.inl ⟨_, _, h, rfl⟩,
    mpr := λ hmpr ↦ match hmpr with
      | Or.inl ⟨_c₂, _s₂, h₁, h₂⟩ => h₂ ▸ small_step.catₙₛ h₁
      | Or.inr ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ small_step.cat₀ₛ
  }

theorem cond_eq:
  ((if b then c₁ else c₂ end, s) =>ₛ conf)
    = (b s ∧ conf = (c₁, s) ∨ b s = false ∧ conf = (c₂, s)) :=
  propext {
    mp := λ hmp ↦ match hb: b s with
      | false => match hmp with | small_step.ifₛ => Or.inr ⟨rfl, hb ▸ rfl⟩
      | true => match hmp with | small_step.ifₛ => Or.inl ⟨rfl, hb ▸ rfl⟩,
    mpr := λ hmpr ↦
      let hss: conf = (bif b s then c₁ else c₂, s) :=
        match hb: b s with
        | true => match hb ▸ hmpr with | Or.inl ⟨_, h₂⟩ => h₂
        | false => match hb ▸ hmpr with | Or.inr ⟨_, h₂⟩ => h₂
      hss ▸ small_step.ifₛ
  }

theorem cond_false (hb: b s₁ = false):
  ((if b then c₁ else c₂ end, s₁) =>ₛ conf) = (conf = (c₂, s₁)) :=
  propext {
    mp := λ hmp ↦ match hb ▸ cond_eq ▸ hmp with
      | Or.inr ⟨_, h₂⟩ => h₂,
    mpr := λ hmpr ↦ cond_eq ▸ Or.inr ⟨hb, hmpr⟩
  }

infixl:10 " =>ₛ* " => RTL small_step

theorem star.demo₂:
  ([|x := 2; while 0 ≤ x loop x := x + 1 end|], s₀) =>ₛ*
      ([|while 0 ≤ x loop x := x + 1 end|], s₀["x" ← 2]) :=
  RTL.head (small_step.catₙₛ small_step.assₛ) (RTL.head small_step.cat₀ₛ RTL.refl)

theorem star.cat_skip_cat
  (hc₁: (c₁, s₁) =>ₛ* (skip₁, s₂)):
  (c₁++c₂, s₁) =>ₛ* (skip₁++c₂, s₂) :=
  RTL.lift (λ (c₁, s) ↦ (c₁++c₂, s)) (λ h ↦ small_step.catₙₛ h) hc₁

theorem star.cat
  (hc₁: (c₁, s₁) =>ₛ* (skip₁, s₂))
  (hc₂: (c₂, s₂) =>ₛ* (skip₁, s₃)):
  (c₁++c₂, s₁) =>ₛ* (skip₁, s₃) :=
  RTL.trans (cat_skip_cat hc₁) (RTL.trans (RTL.single small_step.cat₀ₛ) hc₂)

theorem star.cat_no_influence
  (hc₁: (c₁, s) =>ₛ* (skip₁, s₁)):
  (c₁++c₂, s) =>ₛ* (c₂, s₁) :=
  RTL.trans (cat_skip_cat hc₁) (RTL.single small_step.cat₀ₛ)

end Structural
end Com
