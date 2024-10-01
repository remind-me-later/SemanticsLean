import Semantics.Imp.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
inductive step: Bexp → State → Bool → Prop
  | trueₙ: step true₁ _ true
  | falseₙ: step false₁ _ false
  | notₙ (h: step a s n):
    step (!a) s (!n)
  | andₙ (h₁: step a s n) (h₂: step b s m):
    step (a && b) s (n && m)
  | orₙ (h₁: step a s n) (h₂: step b s m):
    step (a || b) s (n || m)
  | eqₙ: step (a == b) s (a⇓s == b⇓s)
  | leₙ: step (a <= b) s (a⇓s <= b⇓s)

notation s " ⊢ " b " ⟹ " v => step b s v

end Natural

-- Denotational semantics of Bexp
@[reducible, simp]
def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | true₁    => true
  | false₁   => false
  | not₁ b   => !reduce b s
  | and₁ a b => reduce a s && reduce b s
  | or₁ a b  => reduce a s || reduce b s
  | eq₁ a b  => a.reduce s == b.reduce s
  | le₁ a b  => a.reduce s <= b.reduce s

infix:100 "⇓" => reduce

-- relational definition is equivalent to recursive
theorem Natural.from_reduce {b: Bexp} (h: b⇓s = x): s ⊢ b ⟹ x :=
  by induction b generalizing x with
  | true₁ => exact h ▸ step.trueₙ
  | false₁ => exact h ▸ step.falseₙ
  | not₁ a ih => exact h ▸ step.notₙ (ih rfl)
  | and₁ a b iha ihb => exact h ▸ step.andₙ (iha rfl) (ihb rfl)
  | or₁ a b iha ihb => exact h ▸ step.orₙ (iha rfl) (ihb rfl)
  | eq₁ => exact h ▸ step.eqₙ
  | le₁ => exact h ▸ step.leₙ

theorem reduce.from_natural {b: Bexp} (h: s ⊢ b ⟹ x): b⇓s = x :=
  by induction h with
  | notₙ _ ih => exact ih ▸ rfl
  | andₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | orₙ _ _ iha ihb => exact iha ▸ ihb ▸ rfl
  | _ => rfl

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
    simp [step_eq_reduce] at h
    exact h.right
  . simp [Setoid.r] at *
    simp [step_eq_reduce, h]

end Bexp
