import Semantics.Imp.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
inductive step: Bexp → State → Bool → Prop
  | tt: step tt _ true
  | ff: step ff _ false
  | not (h: step a s n):
    step (!a) s (!n)
  | and (h₁: step a s n) (h₂: step b s m):
    step (a && b) s (n && m)
  | or (h₁: step a s n) (h₂: step b s m):
    step (a || b) s (n || m)
  | eq: step (a == b) s (a⇓s == b⇓s)
  | le: step (a <= b) s (a⇓s <= b⇓s)

notation s " ⊢ " a " ⟹ " v => step a s v

end Natural

-- Denotational semantics of Bexp
@[reducible, simp]
def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | tt      => true
  | ff      => false
  | not b   => !reduce b s
  | and a b => reduce a s && reduce b s
  | or a b  => reduce a s || reduce b s
  | eq a b  => a.reduce s == b.reduce s
  | le a b  => a.reduce s <= b.reduce s

infix:100 "⇓" => reduce

-- relational definition is equivalent to recursive
theorem Natural.from_reduce {b: Bexp} (h: b⇓s = x): s ⊢ b ⟹ x :=
  by induction b generalizing x with
  | tt => exact h ▸ step.tt
  | ff => exact h ▸ step.ff
  | not a ih => exact h ▸ step.not (ih rfl)
  | and a b iha ihb => exact h ▸ step.and (iha rfl) (ihb rfl)
  | or a b iha ihb => exact h ▸ step.or (iha rfl) (ihb rfl)
  | eq => exact h ▸ step.eq
  | le => exact h ▸ step.le

theorem reduce.from_natural {b: Bexp} (h: s ⊢ b ⟹ x): b⇓s = x :=
  by induction h with
  | not _ ih => exact ih ▸ rfl
  | and _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | or _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | _ => rfl

@[simp]
theorem step_eq_reduce {b: Bexp}: (s ⊢ b ⟹ x) ↔ b⇓s = x :=
  ⟨reduce.from_natural, Natural.from_reduce⟩

theorem not_true_eq_false: (!b⇓s) = (!b)⇓s := by simp

protected instance step.equiv: Setoid Bexp where
  r a b := ∀ s n, Natural.step a s n = Natural.step b s n
  iseqv := {
    refl := fun _ _ _ => rfl
    symm := fun h s n => (h s n).symm
    trans := fun h1 h2 x n => (h1 x n) ▸ (h2 x n)
  }

@[reducible, simp]
instance reduce.equiv: Setoid Bexp where
  r a b:= ∀s, a⇓s = b⇓s
  iseqv := ⟨fun _ _ => rfl, (Eq.symm $ · ·), fun h1 h2 s => (h1 s) ▸ (h2 s)⟩

protected theorem step_eq_eq_reduce_eq:
  step.equiv.r a b ↔ reduce.equiv.r a b := by
  constructor <;> intro h
  . simp [Setoid.r] at *
    intro s
    specialize h s
    rw [h.right]
  . simp [Setoid.r] at *
    simp [h]

end Bexp
