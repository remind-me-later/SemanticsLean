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
theorem 𝔹.Nat.from_red {b: 𝔹} (h: b↓s = x): (b,s) ⟹ x :=
  by induction b generalizing x with
  | tt => exact h ▸ Nat.tt₁
  | ff => exact h ▸ Nat.ff₁
  | eq => exact h ▸ Nat.eq₁
  | le => exact h ▸ Nat.le₁
  | not _ ih => exact h ▸ Nat.not₁ (ih rfl)
  | and _ _ l r => exact h ▸ Nat.and₁ (l rfl) (r rfl)
  | or _ _  l r => exact h ▸ Nat.or₁  (l rfl) (r rfl)

theorem 𝔹.red.from_Nat {bs: 𝔹 × 𝕊} (h: bs ⟹ x): red.uncurry bs = x :=
  by induction h with
  | tt₁ => rfl
  | ff₁ => rfl
  | eq₁ => rfl
  | le₁ => rfl
  | not₁ _ ih => exact ih ▸ rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

@[simp] theorem 𝔹.Nat_eq_red {b: 𝔹}: (b,s) ⟹ r ↔ b↓s = r := ⟨red.from_Nat, Nat.from_red⟩

theorem 𝔹.not_true_eq_false: (!b↓s) = (¬ₛb)↓s := by simp

protected instance 𝔹.Nat.equiv: Setoid 𝔹 where
  r a b := ∀ s n, (a,s) ⟹ n ↔ (b,s) ⟹ n
  iseqv := {
    refl := λ _ _ _ ↦ Iff.refl _
    symm := λ h s n ↦ Iff.symm (h s n)
    trans := λ h₁ h₂ x n ↦ Iff.trans (h₁ x n) (h₂ x n)
  }

instance 𝔹.red.equiv: Setoid 𝔹 where
  r a b := ∀ s, a.red s = b.red s
  iseqv := {
    refl := λ _ _ ↦ Eq.refl _
    symm := λ h s ↦ Eq.symm (h s)
    trans := λ h₁ h₂ s ↦ h₁ s ▸ h₂ s
  }

protected theorem 𝔹.Nat_eq_eq_red_eq: 𝔹.Nat.equiv.r a b ↔ 𝔹.red.equiv.r a b :=
  by
  constructor <;> intro h s
  . specialize h s (red b s)
    simp at h
    assumption
  . specialize h s
    simp [h]
