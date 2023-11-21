import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

@[reducible]
inductive ℂ.γ: ℂ → 𝕊 → ℂ → 𝕊 → Prop
  | ass₁:
    γ (x ≔ a) s skip (s⟦x↦a.ρ s⟧)

  | cat₁:
    γ (skip;;c) s c s

  | cat₂ (h: γ c s e t):
    γ (c;;d) s (e;;d) t

  | ife₁:
    γ (ife b c d) s (cond (b.ρ s) c d) s

  | wle₁:
    γ (wle b c) s (cond (b.ρ s) (c;;wle b c) skip) s

example:
  ℂ.γ ⟪x ≔ 2; while 0 ≤ x {x≔x-1}⟫ ⟦⟧
      ⟪skip; while 0 ≤ x {x≔x-1}⟫ ⟦"x"↦2⟧ :=
  by
    constructor
    constructor

inductive ℂ.τ: ℂ → 𝕊 → ℂ → 𝕊 → Prop
  | refl:
    τ c s c s

  | step (h₁: γ cx sx cy sy) (h₂: τ cy sy cz sz):
    τ cx sx cz sz

example:
  ℂ.τ ⟪x ≔ 2; while 0 ≤ x {x≔x-1}⟫ ⟦⟧
      ⟪while 0 ≤ x {x≔x-1}⟫ (⟦"x"↦2⟧⟦"x"↦1⟧) :=
  by repeat constructor

theorem ℂ.τ.self (h: γ cx sx cy sy):
  τ cx sx cy sy :=
  by {
    constructor
    . assumption
    . constructor
  }

theorem ℂ.τ.trans
  cy sy
  (h₁: τ cx sx cy sy)
  (h₂: τ cy sy cz sz):
  τ cx sx cz sz :=
  by {
    induction h₁
    . assumption
    . constructor
      . assumption
      . rename_i ih₂
        apply ih₂
        assumption
  }

theorem ℂ.τ.trans'
  (h: τ cx sx cz sz):
  ∃ cy sy, (τ cx sx cy sy) ∧
  (τ cy sy cz sz) :=
  by {
    cases h
    exists cx
    exists sx
    simp
    constructor
    rename_i cy sy h₁ h₂
    exists cy
    exists sy
    constructor
    apply self
    assumption
    assumption
  }

theorem ℂ.τ.unstep
  cy sy
  (h₁: τ cx sx cy sy) (h₂: γ cy sy cz sz):
  τ cx sx cz sz := by
  {
    apply trans cy sy h₁
    apply self h₂
  }

theorem ℂ.τ.final (h: τ c s c₁ s₁):
  ∃d s₂, γ d s₂ c₁ s₁ :=
  by {
    generalize hs: skip = ss at h
    induction h <;> cases hs
    . rename_i c s
      exists skip;;c
      exists s
      constructor
    . rename_i ih
      apply ih
  }

instance ℂ.τ.equiv: Setoid ℂ where
  r c d := ∀ s t, τ c s skip t ↔ τ d s skip t
  iseqv := {
    refl := by simp
    symm := by {
      intro _ _ h _ _
      apply Iff.symm
      apply h
    }
    trans := by {
      intro _ _ _ h₁ h₂ x _
      specialize h₁ x
      specialize h₂ x
      rw [h₁, h₂]
      simp
    }
  }

theorem ℂ.τ.cat_skip_cat
  (h: τ c₁ s skip s₁):
  τ (c₁;;c₂) s (skip;;c₂) s₁ :=
  by {
    generalize hs: skip = ss at h
    induction h <;> cases hs
    . constructor
    . {
      simp at *
      rename_i _ _ ih
      apply step _ ih
      constructor
      assumption
    }
  }

theorem ℂ.τ.cat
  s₁
  (h₁: τ c₁ s skip s₁)
  (h₂: τ c₂ s₁ skip s₂):
  τ (c₁;;c₂) s skip s₂ :=
  by {
    apply trans (skip;;c₂) s₁
    . apply cat_skip_cat h₁
    . apply trans c₂ s₁ _ h₂
      apply self
      constructor
  }

theorem ℂ.τ.cat_no_influence
  (h: τ c₁ s skip s₁):
  τ (c₁;;c₂) s c₂ s₁ :=
  by
    generalize hs: skip = ss at h
    induction h <;> cases hs
    . apply self; constructor
    . {
      simp at *
      rename_i _ _ ih
      apply step _ ih
      constructor
      assumption
    }

theorem ℂ.τ.skipl: c ≈ (skip;;c) :=
  by {
      intro s t
      constructor
      . intro h
        apply trans c s
        . apply self
          constructor
        . assumption
      . intro h
        cases h
        rename_i h₁ h₂
        cases h₁
        . assumption
        . rename_i h
          cases h
  }

theorem ℂ.τ.catex
  (h: τ (c₁;;c₂) s skip s₂):
  ∃s₁, τ c₁ s skip s₁ ∧ τ c₂ s₁ skip s₂ :=
  by {
    sorry
  }


theorem ℂ.τ.skipr: c ≈ (c;;skip) :=
  by {
    intro s t
    constructor
    . intro h
      apply cat t
      . assumption
      . constructor
    . intro h
      have hh := catex h
      cases hh
      rename_i w h
      cases h
      rename_i left right
      cases right
      . assumption
      . rename_i h₁ h₂
        cases h₁
  }
