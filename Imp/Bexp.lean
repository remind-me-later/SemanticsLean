import Imp.State
import Imp.Aexp
import Imp.Syntax

-- Operational semantics of 𝔹
inductive 𝔹.Nat: 𝔹 × 𝕊 → Bool → Prop
  | tt₁:
    Nat (tt, _) true

  | ff₁:
    Nat (ff, _) false

  | eq₁:
    Nat (a =ₛ b, s) (a↓s = b↓s)

  | le₁:
    Nat (a ≤ₛ b, s) (a↓s ≤ b↓s)

  | not₁ {a: 𝔹} (h: Nat (a,s) n):
    Nat (¬ₛa, s) (!n)

  | and₁ {a b: 𝔹} (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (a ∧ₛ b, s) (n && m)

  | or₁ {a b: 𝔹} (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (a ∨ₛ b, s) (n || m)

infix:110 " ⟹ " => 𝔹.Nat

-- Denotational semantics of 𝔹
@[reducible, simp] def 𝔹.red (b: 𝔹) (s: 𝕊): Bool :=
  match b with
  | tt     => true
  | ff     => false
  | ¬ₛb    => !red b s
  | a ∧ₛ b => red a s && red b s
  | a ∨ₛ b => red a s || red b s
  | a =ₛ b => a↓s = b↓s
  | a ≤ₛ b => a↓s ≤ b↓s

infix:110 "↓" => 𝔹.red

-- relational definition is equivalent to recursive
@[simp] theorem 𝔹.Nat.from_red {b: 𝔹} (h: b↓s = x): (b,s) ⟹ x :=
  by induction b generalizing x with
  | tt => unfold red at h; exact h ▸ Nat.tt₁
  | ff => cases h; unfold red; exact Nat.ff₁
  | eq => cases h; unfold red; exact Nat.eq₁
  | le => cases h; unfold red; exact Nat.le₁
  | not _ ih => cases h; unfold red; exact Nat.not₁ (ih rfl)
  | and _ _ l r => cases h; unfold red; exact Nat.and₁ (l rfl) (r rfl)
  | or _ _  l r => cases h; unfold red; exact Nat.or₁  (l rfl) (r rfl)

@[simp] theorem 𝔹.red.from_Nat {bs: 𝔹 × 𝕊} (h: bs ⟹ x): red.uncurry bs = x :=
  by induction h with
  | tt₁ => unfold Function.uncurry red; rfl
  | ff₁ => unfold Function.uncurry red; rfl
  | eq₁ => unfold Function.uncurry red; rfl
  | le₁ => unfold Function.uncurry red; rfl
  | not₁ _ ih => unfold Function.uncurry red; exact ih ▸ rfl
  | _ _ _ ih₁ ih₂ => unfold Function.uncurry red; exact ih₁ ▸ ih₂ ▸ rfl

@[simp] theorem 𝔹.Nat_eq_red {b: 𝔹}: (b,s) ⟹ r ↔ b↓s = r := ⟨red.from_Nat, Nat.from_red⟩

theorem 𝔹.not_true_eq_false {b: 𝔹}:
  !b↓s = ((¬ₛb)↓s) := by simp; cases b↓s <;> simp

protected instance 𝔹.Nat.equiv: Setoid 𝔹 where
  r a b := ∀ s n, (a,s) ⟹ n ↔ (b,s) ⟹ n
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
    }
  }

instance 𝔹.red.equiv: Setoid 𝔹 where
  r a b := ∀ s, a.red s = b.red s
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

protected theorem 𝔹.Nat_eq_eq_red_eq: 𝔹.Nat.equiv.r a b ↔ 𝔹.red.equiv.r a b :=
  by
    constructor <;> intro h s
    . specialize h s (red b s)
      simp at h; assumption
    . intro _; specialize h s
      simp; rw [h]
