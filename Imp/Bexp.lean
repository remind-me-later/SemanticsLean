import Imp.State
import Imp.Aexp
import Imp.Syntax

-- Operational semantics of 𝔹
inductive 𝔹.ε: 𝔹 → 𝕊 → Bool → Prop
  | tt:
    ε tt _ true

  | ff:
    ε ff _ false

  | eq:
    ε (a =ₛ b) s (a.ρ s = b.ρ s)

  | le:
    ε (a ≤ₛ b) s (a.ρ s ≤ b.ρ s)

  | not {a: 𝔹} {h: a.ε s n}:
    ε (¬ₛa) s (¬n)

  | and {a b: 𝔹} {hₗ: a.ε s n} {hᵣ: b.ε s m}:
    ε (a ∧ₛ b) s (n ∧ m)

  | or {a b: 𝔹} {hₗ: a.ε s n} {hᵣ: b.ε s m}:
    ε (a ∨ₛ b) s (n ∨ m)

-- Denotational semantics of 𝔹
@[simp] def 𝔹.ρ (b: 𝔹) (s: 𝕊): Bool :=
  match b with
  | tt     => true
  | ff     => false
  | not b  => ¬b.ρ s
  | a ∧ₛ b => a.ρ s ∧ b.ρ s
  | a ∨ₛ b => a.ρ s ∨ b.ρ s
  | a =ₛ b => a.ρ s = b.ρ s
  | a ≤ₛ b => a.ρ s ≤ b.ρ s

-- relational definition is equivalent to recursive
@[simp] theorem 𝔹.ε_eq_ρ: ε b s r ↔ b.ρ s = r :=
  by
    constructor
    . intro h; induction h with
      | tt => rfl
      | ff => rfl
      | eq => rfl
      | le => rfl
      | not ih => cases ih; rfl
      | _ ih₁ ih₂ => cases ih₁; cases ih₂; rfl
    . revert r
      induction b with
        | tt => intro _ h; cases h; constructor
        | ff => intro _ h; cases h; constructor
        | eq => intro _ h; cases h; constructor
        | le => intro _ h; cases h; constructor
        | not _ ih =>
          intro _ h; cases h; constructor
          apply ih; rfl
        | _ _ _ ih₁ ih₂ =>
          intro _ h; cases h; constructor
          . apply ih₁; rfl
          . apply ih₂; rfl

theorem 𝔹.not_true_eq_false:
  !(ρ b s) = ρ (¬ₛb) s := by simp; cases b.ρ s <;> simp

protected instance 𝔹.ε.equiv: Setoid 𝔹 where
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

instance 𝔹.ρ.equiv: Setoid 𝔹 where
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

protected theorem 𝔹.ε_eq_eq_ρ_eq: 𝔹.ε.equiv.r a b ↔ 𝔹.ρ.equiv.r a b :=
  by
    constructor <;> intro h s
    . specialize h s (ρ b s)
      simp at h; assumption
    . intro _; specialize h s
      simp; rw [h]; simp
