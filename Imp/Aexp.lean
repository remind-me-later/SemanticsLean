import Imp.State
import Imp.Syntax

-- Operational semantics of aexp
inductive 𝔸.ε: 𝔸 → 𝕊 → Int → Prop
  | num:
    ε (num n) _ n

  | loc:
    ε (loc x) s (s.ρ x)

  | add (h₁: a.ε s n) (h₂: b.ε s m):
    ε (a + b) s (n + m)

  | sub (h₁: a.ε s n) (h₂: b.ε s m):
    ε (a - b) s (n - m)

  | mul (h₁: a.ε s n) (h₂: b.ε s m):
    ε (a * b) s (n * m)

-- Denotational semantics of arithmetic expressions
@[reducible] def 𝔸.ρ (a: 𝔸) (s: 𝕊): Int :=
  match a with
  | num n => n
  | loc x => s.ρ x
  | a + b => a.ρ s + b.ρ s
  | a - b => a.ρ s - b.ρ s
  | a * b => a.ρ s * b.ρ s

-- relational definition is equal to recursive
@[simp] theorem 𝔸.ε_eq_ρ (a: 𝔸): a.ε s n ↔ a.ρ s = n :=
  by
    constructor
    . intro h; induction h with
      | num => rfl
      | loc => rfl
      | _ _ _ ih₁ ih₂ => unfold ρ; rw [ih₁, ih₂]
    . revert n; induction a with
      | num _ => intro _ h; cases h; constructor
      | loc _ => intro _ h; cases h; constructor
      | _ _ _ ih₁ ih₂ =>
        intro _ h; cases h; constructor
        . apply ih₁; rfl
        . apply ih₂; rfl

@[simp] theorem 𝔸.ε_eq_ρ' (a: 𝔸): a.ε s (a.ρ s) := by simp

protected instance 𝔸.ε.equiv: Setoid 𝔸 where
  r a b := ∀ s n, ε a s n ↔ ε b s n
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

instance 𝔸.ρ.equiv: Setoid 𝔸 where
  r a b := ∀ s, a.ρ s = b.ρ s
  iseqv := {
    refl := by simp
    symm := by {
      intro _ _ h _
      apply Eq.symm
      apply h
    }
    trans := by {
      intro _ _ _ h₁ h₂ x
      specialize h₁ x
      specialize h₂ x
      rw [h₁, h₂]
    }
  }

protected theorem 𝔸.ε_eq_eq_ρ_eq: 𝔸.ε.equiv.r a b ↔ 𝔸.ρ.equiv.r a b :=
  by
    constructor <;> intro h s
    . specialize h s (ρ b s)
      simp at h; rw [h]
    . simp; rw [h]; simp
