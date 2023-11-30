import Semantics.Imp.Untyped.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
inductive Step: Bexp × State → Bool → Prop
  | tt₁:
    Step (tt, _) true

  | ff₁:
    Step (ff, _) false

  | eq₁:
    Step (eq a b, s) (a⇓s = b⇓s)

  | le₁:
    Step (le a b, s) (a⇓s ≤ b⇓s)

  | not₁ {a: Bexp} (h: Step (a,s) n):
    Step (not a, s) (!n)

  | and₁ {a b: Bexp} (h₁: Step (a,s) n) (h₂: Step (b,s) m):
    Step (and a b, s) (n && m)

  | or₁ {a b: Bexp} (h₁: Step (a,s) n) (h₂: Step (b,s) m):
    Step (or a b, s) (n || m)

infix:110 " ⟹ " => Step

end Natural

-- Denotational semantics of Bexp
@[reducible, simp] def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | tt      => true
  | ff      => false
  | not b   => !reduce b s
  | and a b => reduce a s && reduce b s
  | or a b  => reduce a s || reduce b s
  | eq a b  => a⇓s = b⇓s
  | le a b  => a⇓s ≤ b⇓s

infix:110 "⇓" => reduce

-- relational definition is equivalent to recursive
theorem Natural.from_reduce {b: Bexp} (h: b⇓s = x): (b, s) ⟹ x :=
  by induction b generalizing x with
  | tt => exact h ▸ Step.tt₁
  | ff => exact h ▸ Step.ff₁
  | eq => exact h ▸ Step.eq₁
  | le => exact h ▸ Step.le₁
  | not _ ih => exact h ▸ Step.not₁ (ih rfl)
  | and _ _ l r => exact h ▸ Step.and₁ (l rfl) (r rfl)
  | or _ _  l r => exact h ▸ Step.or₁  (l rfl) (r rfl)

theorem reduce.from_natural {bs: Bexp × State} (h: bs ⟹ x): reduce.uncurry bs = x :=
  by induction h with
  | tt₁ => rfl
  | ff₁ => rfl
  | eq₁ => rfl
  | le₁ => rfl
  | not₁ _ ih => exact ih ▸ rfl
  | _ _ _ ih₁ ih₂ => exact ih₁ ▸ ih₂ ▸ rfl

@[simp] theorem Step_eq_reduce {b: Bexp}: (b,s) ⟹ r ↔ b⇓s = r := ⟨reduce.from_natural, Natural.from_reduce⟩

theorem not_true_eq_false: (!b⇓s) = (not b)⇓s := by simp

protected instance Step.equiv: Setoid Bexp where
  r a b := ∀ s n, (a, s) ⟹ n = (b, s) ⟹ n
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

@[reducible, simp]
instance reduce.equiv: Setoid Bexp where
  r a b:= ∀s, a⇓s = b⇓s
  iseqv := ⟨λ _ _ ↦ Eq.refl _, (Eq.symm $ · ·) , λ h₁ h₂ s ↦ (h₁ s) ▸ (h₂ s)⟩

protected theorem Step_eq_eq_reduce_eq: Step.equiv.r a b ↔ reduce.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    intro s
    specialize h s
    exact h
  . simp [Setoid.r] at *
    simp [h]

end Bexp
