import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax 

-- Semantics of commands.
inductive cevalₒₛ: Com → Σ → Σ → Prop 
  | skipₒₛ (σ: Σ):
    cevalₒₛ skipᵢ σ σ

  | assₒₛ (x: String) (a: Aexp) (σ: Σ):
    cevalₒₛ (x ≔ᵢ a) σ (σ⟦x↦A⟦a⟧ σ⟧)

  | seqₒₛ (σ σ₁ σ₂: Σ) (c₁ c₂: Com)
    (hc₁: cevalₒₛ c₁ σ σ₂) (hc₂: cevalₒₛ c₂ σ₂ σ₁):
    cevalₒₛ (c₁ ;ᵢ c₂) σ σ₁ 

  | if_ttₒₛ (σ σ₁: Σ) (b: Bexp) (c₁ c₂: Com)
    (hb: B⟦b⟧ σ = true) (hc₁: cevalₒₛ c₁ σ σ₁):
    cevalₒₛ (ifᵢ b thenᵢ c₁ elseᵢ c₂ endᵢ) σ σ₁

  | if_ffₒₛ (σ σ₁: Σ) (b: Bexp) (c₁ c₂: Com)
    (hb: B⟦b⟧ σ = false) (hc₂: cevalₒₛ c₂ σ σ₁):
    cevalₒₛ (ifᵢ b thenᵢ c₁ elseᵢ c₂ endᵢ) σ σ₁

  | while_ttₒₛ (σ σ₁ σ₂: Σ) (b: Bexp) (c: Com)
    (hb: B⟦b⟧ σ = true) (hc: cevalₒₛ c σ σ₂) (hW: cevalₒₛ (Com.whilec b c) σ₂ σ₁):
    cevalₒₛ (whileᵢ b doᵢ c endᵢ) σ σ₁

  | while_ffₒₛ (σ: Σ) (b: Bexp) (c: Com)
    (hb: B⟦b⟧ σ = false):
    cevalₒₛ (whileᵢ b doᵢ c endᵢ) σ σ

notation "⟨" c "," σ "⟩" " ⟶ " σ₁ => cevalₒₛ c σ σ₁

example: ⟨⦃x ≔ 5⦄,⟦⟧⟩ ⟶ ⟦"x"↦5⟧ := by apply cevalₒₛ.assₒₛ

example:
  ⟨⦃
    x ≔ 2;
    if x ≤ 1 then
      y ≔ 3
    else
      z ≔ 4
    end
    ⦄, ⟦⟧
  ⟩ ⟶
  ⟦"x"↦2⟧⟦"z"↦4⟧ := 
  by 
    apply cevalₒₛ.seqₒₛ
    case hc₁ => apply cevalₒₛ.assₒₛ
    case hc₂ =>
      apply cevalₒₛ.if_ffₒₛ
      case hb => rfl
      case hc₂ => apply cevalₒₛ.assₒₛ

#check ⟦"x"↦4⟧⟦"x"↦3⟧

def cexp_equiv (c₁ c₂: Com):=
  ∀ (σ σ₁: Σ), (⟨c₁, σ⟩ ⟶ σ₁) ↔ (⟨c₂, σ⟩ ⟶ σ₁) 

theorem while_true_nonterm 
  (σ σ₁: Σ) (c: Com) (b: Bexp) (heqb: b ∼ trueᵢ):
  ¬(⟨whileᵢ b doᵢ c endᵢ, σ⟩ ⟶ σ₁) :=
  by
    intro h
    generalize heqcw: whileᵢ b doᵢ c endᵢ = cw at h
    induction h with
    | skipₒₛ => simp at heqcw
    | assₒₛ => simp at heqcw
    | seqₒₛ => simp at heqcw
    | if_ttₒₛ => simp at heqcw
    | if_ffₒₛ => simp at heqcw
    | while_ttₒₛ _ _ _ _ _ _ _ _ _ ih₂ => {
        simp at heqcw
        apply ih₂
        rw [←heqcw.left, ←heqcw.right]
      }
    | while_ffₒₛ σ _ _ hb => {
        simp at heqcw
        unfold bexp_equiv at heqb
        specialize heqb σ
        simp at heqb
        rw [←heqcw.left, heqb] at hb
        simp at hb
      }

#print axioms while_true_nonterm

theorem cevalₒₛ_determ (c: Com) (σ σ₁ σ₁': Σ)
  (h₁: ⟨c, σ⟩ ⟶ σ₁) (h₂:⟨c, σ⟩ ⟶ σ₁') :
  σ₁ = σ₁' :=
  by
    revert σ₁'
    induction h₁ with
    | skipₒₛ => intro _ h; cases h; rfl
    | assₒₛ  => intro _ h; cases h; rfl
    | seqₒₛ _ _ σ₂ _ _ _ _ ih₁ ih₂ => {
        intro _ h
        apply ih₂
        cases h with
        | seqₒₛ _ _ σ₂' _ _ hc₁ hc₂ => {
            suffices hi : σ₂ = σ₂' by rw [←hi] at hc₂; apply hc₂
            apply ih₁
            assumption
          }
      }
    | if_ttₒₛ _ _ _ _ _ hb _ ih => {
        intro _ h
        apply ih
        cases h with
        | if_ttₒₛ => assumption
        | if_ffₒₛ _ _ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    | if_ffₒₛ _ _ _ _ _ hb _ ih => {
        intro _ h
        apply ih
        cases h with
        | if_ttₒₛ _ _ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
        | if_ffₒₛ _ _ _ _ _ hb₁ => assumption
      }
    | while_ttₒₛ _ _ σ₂ _ _ hb _ _ ih₁ ih => {
        intro _ h
        apply ih
        cases h with
        | while_ttₒₛ  _ _ σ₃ _ _ _ _ hW₁ => {
          suffices hi: σ₂ = σ₃ by rw [←hi] at hW₁; apply hW₁
          apply ih₁
          assumption
        }
        | while_ffₒₛ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    | while_ffₒₛ _ _ _ hb => {
        intro _ h
        cases h with
        | while_ffₒₛ => rfl
        | while_ttₒₛ _ _ _ _ _ hb₁ => {
          rw [hb] at hb₁
          contradiction
        }
      }
    
#print axioms cevalₒₛ_determ
