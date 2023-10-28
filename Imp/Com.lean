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

  | seq s₂ (hc₁: ε c₁ s s₂) (hc₂: ε c₂ s₂ s₁):
    ε ⦃c₁;c₂⦄ s s₁

  | if_tt (hb: 𝔹.ρ b s = true) (hc₁: ε c₁ s s₁):
    ε ⦃if b {c₁} else {c₂}⦄ s s₁

  | if_ff (hb: 𝔹.ρ b s = false) (hc₂: ε c₂ s s₂):
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
    . apply ℂ.ε.if_ff
      . rfl
      . constructor

def ℂ.sim c₁ c₂ := ∀ s s₁, (ε c₁ s s₁) ↔ (ε c₂ s s₁)

theorem ℂ.skipl: sim ⦃skip;c⦄ c := by
    unfold sim
    intro _ _
    constructor
    . intro h
      cases h with | seq _ hc₁ _ => cases hc₁; assumption
    . intro h
      constructor
      . constructor
      . assumption

theorem ℂ.skipr: sim ⦃c;skip⦄ c := by
    unfold sim
    intro _ _
    constructor
    . intro h
      cases h with | seq _ _ hc₂ => cases hc₂; assumption
    . intro h
      constructor
      . assumption
      . constructor

theorem ℂ.if_true (h: 𝔹.sim b ⦃tt⦄):
  sim ⦃if b {c₁} else {c₂}⦄ c₁ :=
  by
    unfold sim
    intro s₁ _
    constructor
    . intro h₁
      cases h₁ with
      | if_tt => assumption
      | if_ff hb => {
        specialize h s₁
        simp at h
        rw [hb] at h
        contradiction
      }
    . intro h₁
      apply ε.if_tt
      . specialize h s₁
        simp at h
        assumption
      . assumption

theorem ℂ.if_false (h: 𝔹.sim b ⦃ff⦄):
  sim ⦃if b {c₁} else {c₂}⦄ c₂ :=
  by
    unfold sim
    intro s₁ s₂
    apply Iff.intro
    . intro h₁
      unfold 𝔹.sim at h
      cases h₁ with
      | if_ff => assumption
      | if_tt hb => {
        specialize h s₁
        simp at h
        rw [hb] at h
        contradiction
      }
    . intro h₁
      unfold 𝔹.sim at h
      apply ε.if_ff
      . specialize h s₁
        simp at h
        assumption
      . assumption

theorem ℂ.while_true (heqb: 𝔹.sim b ⦃tt⦄):
  ¬(ε ⦃while b {c}⦄ s s₁) :=
  by
    intro h
    generalize heqcw: ⦃while b {c}⦄ = cw at h
    induction h with
    | skip  => simp at heqcw
    | ass   => simp at heqcw
    | seq   => simp at heqcw
    | if_tt => simp at heqcw
    | if_ff => simp at heqcw
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
        simp at hb
      }

#print axioms ℂ.while_true

theorem ℂ.ε_determ (h₁: ε c s s₁) (h₂: ε c s s₁'):
  s₁ = s₁' :=
  by
    revert s₁'
    induction h₁ with
    | skip => intro _ h; cases h; rfl
    | ass  => intro _ h; cases h; rfl
    | seq s₂ _ _ ih₁ ih₂ => {
        intro _ h
        apply ih₂
        cases h with
        | seq s₂' hc₁ hc₂ => {
            suffices hi : s₂ = s₂' by rw [←hi] at hc₂; apply hc₂
            apply ih₁
            assumption
          }
      }
    | if_tt hb _ ih => {
        intro _ h
        apply ih
        cases h with
        | if_tt => assumption
        | if_ff hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    | if_ff hb _ ih => {
        intro _ h
        apply ih
        cases h with
        | if_tt hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
        | if_ff hb₁ => assumption
      }
    | while_tt s₂ hb _ _ ih₁ ih => {
        intro _ h
        apply ih
        cases h with
        | while_tt s₃ _ _ hW₁ => {
          suffices hi: s₂ = s₃ by rw [←hi] at hW₁; apply hW₁
          apply ih₁
          assumption
        }
        | while_ff hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    | while_ff hb => {
        intro _ h
        cases h with
        | while_ff => rfl
        | while_tt _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }

#print axioms ℂ.ε_determ
