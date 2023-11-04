import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

-- Semantics of commands.
inductive ℂ.ε: ℂ → 𝕊 → 𝕊 → Prop
  | skip:
    ε skip s s

  | ass:
    ε (x ≔ₛ a) s (𝕊.update s x (𝔸.ρ a s))

  | cat s₂ (hc₁: ε c₁ s s₂) (hc₂: ε c₂ s₂ s₁):
    ε (c₁;ₛc₂) s s₁

  | ite_tt (hb: 𝔹.ρ b s) (hc₁: ε c₁ s s₁):
    ε (ife b c₁ c₂) s s₁

  | ite_ff (hb: 𝔹.ρ b s = false) (hc₂: ε c₂ s s₂):
    ε (ife b c₁ c₂) s s₂

  | wle_tt s₂ (hb: 𝔹.ρ b s) (hc: ε c s s₂) (hw: ε (wle b c) s₂ s₁):
    ε (wle b c) s s₁

  | wle_ff (hb: 𝔹.ρ b s = false):
    ε (wle b c) s s

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

def ℂ.esim c₁ c₂ := ∀ s s₁, ε c₁ s s₁ ↔ ε c₂ s s₁

theorem ℂ.skipl: esim (skip;ₛc) c := by
    unfold esim
    intro _ _
    constructor <;> intro h
    . cases h with | cat _ hc₁ => cases hc₁; assumption
    . constructor
      . constructor
      . assumption

theorem ℂ.skipr: esim (c;ₛskip) c := by
    unfold esim
    intro _ _
    constructor <;> intro h
    . cases h with | cat _ _ hc₂ => cases hc₂; assumption
    . constructor
      . assumption
      . constructor

theorem ℂ.if_true (h: b ≈ 𝔹.tt):
  esim (ife b c₁ c₂) c₁ :=
  by
    unfold esim
    intro s₁ _
    constructor <;> intro h₁
    . cases h₁ with
      | ite_tt => assumption
      | ite_ff hb =>
        rw [h] at hb
        contradiction
    . apply ε.ite_tt
      . apply h
      . assumption

theorem ℂ.if_false (h: b ≈  𝔹.ff):
  esim (ife b c₁ c₂) c₂ :=
  by
    unfold esim
    intro s₁ _
    constructor <;> intro h₁
    . cases h₁ with
      | ite_ff => assumption
      | ite_tt hb =>
        rw [h] at hb
        contradiction

    . apply ε.ite_ff
      . apply h
      . assumption

theorem ℂ.while_true (heqb: b ≈ 𝔹.tt):
  ¬(ε (wle b c) s s₁) :=
  by
    intro h
    generalize heqw: wle b c = w at h
    induction h with
    | wle_tt _ _ _ _ _ ih₂ =>
      simp at heqw
      apply ih₂
      rw [←heqw.left, ←heqw.right]

    | wle_ff hb =>
      simp at heqw
      rw [←heqw.left, heqb] at hb
      contradiction

    | _ => contradiction

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

    | wle_tt s₂ hb _ _ ih₁ ih =>
      intro _ h; apply ih; cases h with
      | wle_tt s₃ =>
        have hi: s₂ = s₃ := by apply ih₁; assumption
        cases hi; assumption
      | wle_ff hb₁ => rw [hb] at hb₁; contradiction

    | wle_ff hb =>
      intro _ h; cases h
      . rw [hb] at *; contradiction
      . rfl

    | _ => intro _ h; cases h; rfl

#print axioms ℂ.ε_determ
