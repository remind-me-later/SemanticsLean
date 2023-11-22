import Imp.State
import Imp.Aexp
import Imp.Syntax

-- Operational semantics of 𝔹
inductive 𝔹.ε: 𝔹 → 𝕊 → Bool → Prop
  | tt₁:
    ε tt _ true

  | ff₁:
    ε ff _ false

  | eq₁:
    ε (a =ₛ b) s (a.ρ s = b.ρ s)

  | le₁:
    ε (a ≤ₛ b) s (a.ρ s ≤ b.ρ s)

  | not₁ {a: 𝔹} (h: a.ε s n):
    ε (¬ₛa) s (¬n)

  | and₁ {a b: 𝔹} (hₗ: a.ε s n) (hᵣ: b.ε s m):
    ε (a ∧ₛ b) s (n ∧ m)

  | or₁ {a b: 𝔹} (hₗ: a.ε s n) (hᵣ: b.ε s m):
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
@[simp] theorem 𝔹.ε.from_ρ (h: b.ρ s = x): ε b s x :=
  by induction b generalizing x with
  | tt => exact h ▸ ε.tt₁
  | ff => exact h ▸ ε.ff₁
  | eq => exact h ▸ ε.eq₁
  | le => exact h ▸ ε.le₁
  | not _ ih => exact h ▸ ε.not₁ (ih rfl)
  | and _ _ l r => exact h ▸ ε.and₁ (l rfl) (r rfl)
  | or _ _  l r => exact h ▸ ε.or₁  (l rfl) (r rfl)

@[simp] theorem 𝔹.ρ.from_ε (h: ε b s x): b.ρ s = x :=
  by induction h with
  | tt₁ => rfl
  | ff₁ => rfl
  | eq₁ => rfl
  | le₁ => rfl
  | not₁ _ ih => exact ih ▸ rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

@[simp] theorem 𝔹.ε_eq_ρ: ε b s r ↔ b.ρ s = r := ⟨ρ.from_ε, ε.from_ρ⟩

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
