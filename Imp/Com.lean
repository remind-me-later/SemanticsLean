import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

-- Semantics of commands.
inductive ℂ.ε: ℂ → 𝕊 → 𝕊 → Prop
  | skip:
    ε ⦃skip⦄ s s

  | ass:
    ε ⦃x ≔ a⦄ s (𝕊.update s x (𝔸.ρ a s))

  | cat s₂ (hc₁: ε c₁ s s₂) (hc₂: ε c₂ s₂ s₁):
    ε ⦃c₁;c₂⦄ s s₁

  | ite_tt (hb: 𝔹.ρ b s = true) (hc₁: ε c₁ s s₁):
    ε ⦃if b {c₁} else {c₂}⦄ s s₁

  | ite_ff (hb: 𝔹.ρ b s = false) (hc₂: ε c₂ s s₂):
    ε ⦃if b {c₁} else {c₂}⦄ s s₂

  | while_tt s₂ (hb: 𝔹.ρ b s = true) (hc: ε c s s₂) (hw: ε ⦃while b {c}⦄ s₂ s₁):
    ε ⦃while b {c}⦄ s s₁

  | while_ff (hb: 𝔹.ρ b s = false):
    ε ⦃while b {c}⦄ s s

example: ℂ.ε ⟪x ≔ 5⟫ ⟦⟧ ⟦x↦5⟧ := by constructor

example:
  ℂ.ε ⟪
    x ≔ 2;
    if x ≤ 1 {
      y ≔ 3
    } else {
      z ≔ 4
    }⟫
  ⟦⟧
  ⟦x↦2, z↦4⟧ :=
  by
    constructor
    . constructor
    . apply ℂ.ε.ite_ff
      . rfl
      . constructor

def ℂ.sim c₁ c₂ := ∀ s s₁, ε c₁ s s₁ ↔ ε c₂ s s₁

theorem ℂ.skipl: sim ⦃skip;c⦄ c := by
    unfold sim
    intro _ _
    constructor <;> intro h
    . cases h with | cat _ hc₁ => cases hc₁; assumption
    . constructor
      . constructor
      . assumption

theorem ℂ.skipr: sim ⦃c;skip⦄ c := by
    unfold sim
    intro _ _
    constructor <;> intro h
    . cases h with | cat _ _ hc₂ => cases hc₂; assumption
    . constructor
      . assumption
      . constructor

theorem ℂ.if_true (h: 𝔹.sim b ⦃tt⦄):
  sim ⦃if b {c₁} else {c₂}⦄ c₁ :=
  by
    unfold sim
    intro s₁ _
    constructor <;> intro h₁
    . cases h₁ with
      | ite_tt => assumption
      | ite_ff hb =>
        specialize h s₁
        simp at h
        rw [hb] at h
        contradiction

    . apply ε.ite_tt
      . specialize h s₁
        simp at h
        assumption
      . assumption

theorem ℂ.if_false (h: 𝔹.sim b ⦃ff⦄):
  sim ⦃if b {c₁} else {c₂}⦄ c₂ :=
  by
    unfold sim
    intro s₁ _
    constructor <;> intro h₁
    . cases h₁ with
      | ite_ff => assumption
      | ite_tt hb =>
        specialize h s₁
        simp at h
        rw [hb] at h
        contradiction

    . apply ε.ite_ff
      . specialize h s₁
        simp at h
        assumption
      . assumption

theorem ℂ.while_true (heqb: 𝔹.sim b ⦃tt⦄):
  ¬(ε ⦃while b {c}⦄ s s₁) :=
  by
    intro h
    generalize heqcw: ⦃while b {c}⦄ = w at h
    induction h with
    | while_tt _ _ _ _ _ ih₂ => {
        simp at heqcw
        apply ih₂
        rw [←heqcw.left, ←heqcw.right]
      }
    | while_ff hb => {
        simp at heqcw
        unfold 𝔹.sim at heqb
        simp at heqb
        rw [←heqcw.left, heqb] at hb
        contradiction
      }
    | _  => simp at heqcw

#print axioms ℂ.while_true

theorem ℂ.ε_determ (h₁: ε c s s₁) (h₂: ε c s s₁'):
  s₁ = s₁' :=
  by
    revert s₁'
    induction h₁ with
    | cat s₂ _ _ ih₁ ih₂ =>
      intro _ h; apply ih₂; cases h with | cat s₂' =>
        have hi: s₂ = s₂' := by apply ih₁; assumption
        cases hi; assumption

    | ite_tt hb _ ih =>
      intro _ h; apply ih; cases h
      . assumption
      . rw [hb] at *; contradiction

    | ite_ff hb _ ih =>
      intro _ h; apply ih; cases h
      . rw [hb] at *; contradiction
      . assumption

    | while_tt s₂ hb _ _ ih₁ ih =>
      intro _ h; apply ih; cases h with
      | while_tt s₃ =>
        have hi: s₂ = s₃ := by apply ih₁; assumption
        cases hi; assumption
      | while_ff hb₁ => rw [hb] at hb₁; contradiction

    | while_ff hb =>
      intro _ h; cases h
      . rw [hb] at *; contradiction
      . rfl

    | _ => intro _ h; cases h; rfl

#print axioms ℂ.ε_determ
