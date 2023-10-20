import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax 

-- Semantics of commands.
inductive ℂ.evₒ: ℂ → Σ → Σ → Prop 
  | skipₒ (σ: Σ):
    evₒ ⦃nop⦄ σ σ

  | assₒ (x: String) (a: 𝔸) (σ: Σ):
    evₒ ⦃.x = .a⦄ σ (State.update σ x ⟪a, σ⟫)

  | seqₒ (σ σ₁ σ₂: Σ) (c₁ c₂: ℂ)
    (hc₁: evₒ c₁ σ σ₂) (hc₂: evₒ c₂ σ₂ σ₁):
    evₒ ⦃.c₁;.c₂⦄ σ σ₁

  | if_ttₒ (σ σ₁: Σ) (b: 𝔹) (c₁ c₂: ℂ)
    (hb: ⟪b, σ⟫ = true) (hc₁: evₒ c₁ σ σ₁):
    evₒ ⦃if .b {.c₁} else {.c₂}⦄ σ σ₁

  | if_ffₒ (σ σ₁: Σ) (b: 𝔹) (c₁ c₂: ℂ)
    (hb: ⟪b, σ⟫ = false) (hc₂: evₒ c₂ σ σ₁):
    evₒ ⦃if .b {.c₁} else {.c₂}⦄ σ σ₁

  | while_ttₒ (σ σ₁ σ₂: Σ) (b: 𝔹) (c: ℂ)
    (hb: ⟪b, σ⟫ = true) (hc: evₒ c σ σ₂) (hW: evₒ ⦃while .b {.c}⦄ σ₂ σ₁):
    evₒ ⦃while .b {.c}⦄ σ σ₁

  | while_ffₒ (σ: Σ) (b: 𝔹) (c: ℂ)
    (hb: ⟪b, σ⟫ = false):
    evₒ ⦃while .b {.c}⦄ σ σ

notation "⟨" c "," σ "⟩" " → " σ₁ => ℂ.evₒ c σ σ₁

example: ⟨⦃x = 5⦄,⟦⟧⟩ → ⟦x↦5⟧ := by apply ℂ.evₒ.assₒ

example:
  ⟨⦃
    x = 2;
    if x <= 1 {
      y = 3
    } else {
      z = 4
    }
    ⦄, ⟦⟧
  ⟩ →
  ⟦x↦2, z↦4⟧ := 
  by 
    apply ℂ.evₒ.seqₒ
    case hc₁ => apply ℂ.evₒ.assₒ
    case hc₂ =>
      apply ℂ.evₒ.if_ffₒ
      case hb => rfl
      case hc₂ => apply ℂ.evₒ.assₒ

def ℂ.sim (c₁ c₂: ℂ):=
  ∀ (σ σ₁: Σ), (⟨c₁, σ⟩ → σ₁) ↔ (⟨c₂, σ⟩ → σ₁) 

notation e₁ " ∼ " e₂ => ℂ.sim e₁ e₂

theorem ℂ.skipl (c: ℂ): ⦃nop;.c⦄ ∼ c := by
    unfold sim
    intro σ σ₁
    apply Iff.intro
    . {
      intro h
      cases h with | seqₒ _ _ _ _ _ hc₁ _ => cases hc₁; assumption
    }
    . {
      intro h
      apply evₒ.seqₒ
      . apply evₒ.skipₒ
      . assumption
    }

theorem ℂ.skipr (c: ℂ): ⦃.c;nop⦄ ∼ c := by
    unfold sim
    intro σ σ₁
    apply Iff.intro
    . {
      intro h
      cases h with | seqₒ _ _ _ _ _ _ hc₂ => cases hc₂; assumption
    }
    . {
      intro h
      apply evₒ.seqₒ
      . assumption
      . apply evₒ.skipₒ
    }

theorem ℂ.if_true (b: 𝔹) (c₁ c₂: ℂ) (h: b ∼ ⦃tt⦄):
  ⦃if .b {.c₁} else {.c₂}⦄ ∼ c₁ :=
  by
    unfold sim
    intro σ₁ σ₂
    apply Iff.intro
    . {
      intro h₁
      unfold 𝔹.sim at h
      cases h₁ with
      | if_ttₒ => assumption
      | if_ffₒ _ _ _ _ _ hb => {
        specialize h σ₁
        simp at h
        rw [hb] at h
        contradiction
      }
    }
    . {
      intro h₁
      unfold 𝔹.sim at h
      apply evₒ.if_ttₒ
      . {
        specialize h σ₁
        simp at h
        assumption
      }
      . assumption
    }

theorem ℂ.if_false (b: 𝔹) (c₁ c₂: ℂ) (h: b ∼ ⦃ff⦄):
  ⦃if .b {.c₁} else {.c₂}⦄ ∼ c₂ :=
  by
    unfold sim
    intro σ₁ σ₂
    apply Iff.intro
    . {
      intro h₁
      unfold 𝔹.sim at h
      cases h₁ with
      | if_ffₒ => assumption
      | if_ttₒ _ _ _ _ _ hb => {
        specialize h σ₁
        simp at h
        rw [hb] at h
        contradiction
      }
    }
    . {
      intro h₁
      unfold 𝔹.sim at h
      apply evₒ.if_ffₒ
      . {
        specialize h σ₁
        simp at h
        assumption
      }
      . assumption
    }



theorem ℂ.while_true 
  (σ σ₁: Σ) (c: ℂ) (b: 𝔹) (heqb: b ∼ ⦃tt⦄):
  ¬(⟨⦃while .b {.c}⦄, σ⟩ → σ₁) :=
  by
    intro h
    generalize heqcw: ⦃while .b {.c}⦄ = cw at h
    induction h with
    | skipₒ  => simp at heqcw
    | assₒ   => simp at heqcw
    | seqₒ   => simp at heqcw
    | if_ttₒ => simp at heqcw
    | if_ffₒ => simp at heqcw
    | while_ttₒ _ _ _ _ _ _ _ _ _ ih₂ => {
        simp at heqcw
        apply ih₂
        rw [←heqcw.left, ←heqcw.right]
      }
    | while_ffₒ σ _ _ hb => {
        simp at heqcw
        unfold 𝔹.sim at heqb
        specialize heqb σ
        simp at heqb
        rw [←heqcw.left, heqb] at hb
        simp at hb
      }

#print axioms ℂ.while_true

theorem ℂ.evₒ_determ (c: ℂ) (σ σ₁ σ₁': Σ)
  (h₁: ⟨c, σ⟩ → σ₁) (h₂: ⟨c, σ⟩ → σ₁') :
  σ₁ = σ₁' := 
  by
    revert σ₁'
    induction h₁ with
    | skipₒ => intro _ h; cases h; rfl
    | assₒ  => intro _ h; cases h; rfl
    | seqₒ _ _ σ₂ _ _ _ _ ih₁ ih₂ => {
        intro _ h
        apply ih₂
        cases h with
        | seqₒ _ _ σ₂' _ _ hc₁ hc₂ => {
            suffices hi : σ₂ = σ₂' by rw [←hi] at hc₂; apply hc₂
            apply ih₁
            assumption
          }
      }
    | if_ttₒ _ _ _ _ _ hb _ ih => {
        intro _ h
        apply ih
        cases h with
        | if_ttₒ => assumption
        | if_ffₒ _ _ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    | if_ffₒ _ _ _ _ _ hb _ ih => {
        intro _ h
        apply ih
        cases h with
        | if_ttₒ _ _ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
        | if_ffₒ _ _ _ _ _ hb₁ => assumption
      }
    | while_ttₒ _ _ σ₂ _ _ hb _ _ ih₁ ih => {
        intro _ h
        apply ih
        cases h with
        | while_ttₒ  _ _ σ₃ _ _ _ _ hW₁ => {
          suffices hi: σ₂ = σ₃ by rw [←hi] at hW₁; apply hW₁
          apply ih₁
          assumption
        }
        | while_ffₒ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    | while_ffₒ _ _ _ hb => {
        intro _ h
        cases h with
        | while_ffₒ => rfl
        | while_ttₒ _ _ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    
#print axioms ℂ.evₒ_determ

