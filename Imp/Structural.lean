import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

import Mathlib.Logic.Relation

-- @[reducible]
inductive ℂ.γ: ℂ × 𝕊 → ℂ × 𝕊 → Prop
  | ass₁:
    γ (x ≔ a, s) (skip, s⟦x↦a.ρ s⟧)

  | cat₁:
    γ (skip;;c, s) (c, s)

  | cat₂ (h: γ (c, s) (e, t)):
    γ (c;;d, s) (e;;d, t)

  | ife₁ (hb: b.ρ s):
    γ (ife b c d, s) (c, s)

  | ife₂ (hb: b.ρ s = false):
    γ (ife b c d, s) (d, s)

  | wle₁:
    γ (wle b c, s) (ife b (c;;wle b c) skip, s)

example:
  ℂ.γ (⟪x ≔ 2; while 0 ≤ x {x≔x-1}⟫, ⟦⟧)
      (⟪skip; while 0 ≤ x {x≔x-1}⟫, ⟦"x"↦2⟧) :=
  by
    repeat constructor

def ℂ.τ := Relation.ReflTransGen γ

example:
  ℂ.τ (⟪x ≔ 2; while 0 ≤ x {x≔x-1}⟫, ⟦⟧)
      (⟪while 0 ≤ x {x≔x-1}⟫, (⟦"x"↦2⟧)) :=
  by
    apply Relation.ReflTransGen.head
    constructor
    constructor
    apply Relation.ReflTransGen.head
    constructor
    apply Relation.ReflTransGen.refl

theorem ℂ.τ.cat_skip_cat
  (h: τ (c₁, s) (skip, s₁)):
  τ (c₁;;c₂, s) (skip;;c₂, s₁) :=
  by {
    apply Relation.ReflTransGen.lift (fun x => (x.fst;;c₂, x.snd)) _ h
    intro a b h
    cases a
    cases b
    constructor
    assumption
  }

theorem ℂ.τ.cat
  s₁
  (h₁: τ (c₁, s) (skip, s₁))
  (h₂: τ (c₂, s₁) (skip, s₂)):
  τ (c₁;;c₂, s) (skip, s₂) :=
  by {
    apply Relation.ReflTransGen.trans
    . apply cat_skip_cat h₁
    . apply Relation.ReflTransGen.trans _ h₂
      apply Relation.ReflTransGen.single
      constructor
  }

theorem ℂ.τ.cat_no_influence
  (h: τ (c₁, s) (skip, s₁)):
  τ (c₁;;c₂, s) (c₂, s₁) :=
  by
    apply Relation.ReflTransGen.trans
    . apply cat_skip_cat h
    . apply Relation.ReflTransGen.single
      constructor

@[simp] theorem ℂ.γ.cat_iff:
  γ (c₁;;c₂, s) et ↔
  (∃e t, γ (c₁, s) (e, t) ∧ et = (e;;c₂, t))
  ∨ (c₁ = skip ∧ et = (c₂, s)) :=
  by {
    constructor <;> intro h
    . {
      cases h
      . {
        apply Or.intro_right
        apply And.intro rfl rfl
      }
      . {
        apply Or.intro_left
        rename_i e t h
        exists e, t
      }
    }
    . {
      cases h <;> rename_i h <;> cases h
      . {
        rename_i e h
        cases h
        rename_i t h
        cases h
        rename_i left right
        cases right
        constructor
        assumption
      }
      . {
        rename_i left right
        cases left
        cases right
        constructor
      }
    }
  }

@[simp] lemma ℂ.γ.ite_iff:
  γ (ife b S T, s) Us ↔
  (b.ρ s ∧ Us = (S, s)) ∨ (b.ρ s = false ∧ Us = (T, s)) :=
  by {
    constructor <;> intro h
    . {
      cases h <;> rename_i hb
      . {
        apply Or.intro_left
        apply And.intro hb rfl
      }
      . {
        apply Or.intro_right
        apply And.intro hb rfl
      }
    }
    . {
      cases h <;> rename_i h <;> cases h <;> rename_i left right <;> cases right
      . apply γ.ife₁ left
      . apply γ.ife₂ left
    }
  }

theorem ℂ.τ.catex
  (h: τ (c₁;;c₂, s) (skip, s₂)):
  ∃s₁, τ (c₁, s) (skip, s₁) ∧ τ (c₂, s₁) (skip, s₂) :=
  by {
    generalize hs₀: (c₁;;c₂, s) = ss₀ at h
    generalize hs₁: (skip, s₂) = ss₁ at h
    induction' h generalizing c₁ c₂ s s₂  <;> cases hs₁ <;> cases hs₀
    cases hs₀
    simp at *
    rename_i ih
  }



-- instance ℂ.τ.equiv: Setoid ℂ where
--   r c d := ∀ s t, τ (c, s) (skip, t) ↔ τ (d, s) (skip, t)
--   iseqv := {
--     refl := by simp
--     symm := by {
--       intro _ _ h _ _
--       apply Iff.symm
--       apply h
--     }
--     trans := by {
--       intro _ _ _ h₁ h₂ x _
--       specialize h₁ x
--       specialize h₂ x
--       rw [h₁, h₂]
--     }
--   }


-- theorem ℂ.τ.skipl: c ≈ (skip;;c) :=
--   by {
--       intro s t
--       constructor
--       . intro h
--         apply Relation.ReflTransGen.trans
--         . apply Relation.ReflTransGen.single
--           constructor
--         . assumption
--       . intro h
--         induction h
--         cases h
--         rename_i h₁ h₂
--         cases h₁
--         . assumption
--         . rename_i h h₁
--           cases h
--           cases h₁

--   }


-- theorem ℂ.τ.skipr: c ≈ (c;;skip) :=
--   by {
--     intro s t
--     constructor
--     . intro h
--       apply cat t
--       . assumption
--       . constructor
--     . intro h
--       have hh := catex h
--       cases hh
--       rename_i w h
--       cases h
--       rename_i left right
--       cases right
--       . assumption
--       . rename_i h₁ h₂
--         cases h₁
--   }
