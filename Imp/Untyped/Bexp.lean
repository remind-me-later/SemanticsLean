import Imp.Untyped.Aexp

namespace Bexp

-- Operational semantics of Bexp
inductive Nat: Bexp × State → Bool → Prop
  | tt₁:
    Nat (tt, _) true

  | ff₁:
    Nat (ff, _) false

  | eq₁:
    Nat (eq a b, s) (a⇓s = b⇓s)

  | le₁:
    Nat (le a b, s) (a⇓s ≤ b⇓s)

  | not₁ {a: Bexp} (h: Nat (a,s) n):
    Nat (not a, s) (!n)

  | and₁ {a b: Bexp} (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (and a b, s) (n && m)

  | or₁ {a b: Bexp} (h₁: Nat (a,s) n) (h₂: Nat (b,s) m):
    Nat (or a b, s) (n || m)

infix:110 " ⟹ " => Nat

-- Denotational semantics of Bexp
@[reducible, simp] def red (b: Bexp) (s: State): Bool :=
  match b with
  | tt      => true
  | ff      => false
  | not b   => !red b s
  | and a b => red a s && red b s
  | or a b  => red a s || red b s
  | eq a b  => a⇓s = b⇓s
  | le a b  => a⇓s ≤ b⇓s

infix:110 "⇓" => red

-- relational definition is equivalent to recursive
theorem Nat.from_red {b: Bexp} (h: b⇓s = x): (b, s) ⟹ x :=
  by induction b generalizing x with
  | tt => exact h ▸ Nat.tt₁
  | ff => exact h ▸ Nat.ff₁
  | eq => exact h ▸ Nat.eq₁
  | le => exact h ▸ Nat.le₁
  | not _ ih => exact h ▸ Nat.not₁ (ih rfl)
  | and _ _ l r => exact h ▸ Nat.and₁ (l rfl) (r rfl)
  | or _ _  l r => exact h ▸ Nat.or₁  (l rfl) (r rfl)

theorem red.from_Nat {bs: Bexp × State} (h: bs ⟹ x): red.uncurry bs = x :=
  by induction h with
  | tt₁ => rfl
  | ff₁ => rfl
  | eq₁ => rfl
  | le₁ => rfl
  | not₁ _ ih => exact ih ▸ rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

@[simp] theorem Nat_eq_red {b: Bexp}: (b,s) ⟹ r ↔ b⇓s = r := ⟨red.from_Nat, Nat.from_red⟩

theorem not_true_eq_false: (!b⇓s) = (not b)⇓s := by simp

protected instance Nat.equiv: Setoid Bexp where
  r a b := ∀ s n, (a, s) ⟹ n = (b, s) ⟹ n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

instance red.equiv: Setoid Bexp := ⟨(red · = red ·), ⟨(Eq.refl $ red ·), Eq.symm, Eq.trans⟩⟩

protected theorem Nat_eq_eq_red_eq: Nat.equiv.r a b ↔ red.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    apply funext
    intro s
    specialize h s
    exact h
  . simp [Setoid.r] at *
    simp [h]

end Bexp