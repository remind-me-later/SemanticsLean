import Semantics.Set

-- Concrete Semantics with Isabelle
-- 10.4.1 The Knaster-Tarski Fixpoint Theorem on Sets

-- define a partial order
class PartialOrder (α: Type) extends LE α, LT α where
  le_refl: ∀a: α, a ≤ a
  le_trans: ∀⦃a b c: α⦄, a ≤ b → b ≤ c → a ≤ c
  le_iff_le_not_le: ∀⦃a b: α⦄, a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_antisymm: ∀⦃a b: α⦄, a ≤ b → b ≤ a → a = b

theorem PartialOrder.le_rfl [PartialOrder α] {a: α}:
  a ≤ a :=
  le_refl a

theorem Set.le_def (a b : Set α) :
  a ≤ b ↔ a ⊆ b := Iff.rfl

instance Set.LT (α: Type): LT (Set α) :=
  {
    lt := λ a b ↦ a ⊆ b ∧ a ≠ b
  }

theorem Set.lt_def (a b : Set α):
  a < b ↔ a ⊆ b ∧ a ≠ b :=
  Iff.rfl

instance Set.partialOrder: PartialOrder (Set α) :=
  {
    le := λ a b ↦ a ⊆ b,
    lt := λ a b ↦ a ⊆ b ∧ a ≠ b,
    le_refl := λ _ _ ha ↦ ha,
    le_antisymm := λ _ _ h₁ h₂ ↦ Subset.antisymm h₁ h₂,
    le_iff_le_not_le := λ _ _ ↦ {
        mp := λ ⟨h₁, h₂⟩ ↦ ⟨h₁, λ h' ↦ h₂ $ Subset.antisymm h₁ h'⟩
        mpr := λ ⟨h₁, h₂⟩ ↦ ⟨h₁, λ h' ↦ h₂ $ Subset.from_eq h'.symm⟩
      }
    le_trans := λ _ _ _ h₁ h₂ _ ha ↦ h₂ (h₁ ha)
  }

class CompleteLattice (α: Type) extends PartialOrder α where
  Inf: Set α → α
  Inf_le: ∀⦃s: Set α⦄, ∀x ∈ s, Inf s ≤ x
  le_Inf: ∀⦃s: Set α⦄ ⦃a: α⦄, (∀b ∈ s, a ≤ b) → a ≤ Inf s

theorem inf_unique [CompleteLattice α]
  (s: Set α) (a b: α)
  (h: CompleteLattice.Inf s = a) (h': CompleteLattice.Inf s = b):
  a = b :=
  PartialOrder.le_antisymm
    (h ▸ h' ▸ PartialOrder.le_refl b)
    (h' ▸ h ▸ PartialOrder.le_refl a)

instance Set.completeLattice: CompleteLattice (Set α) :=
  {
    Inf := λ s ↦ {x | ∀ A ∈ s, x ∈ A},
    Inf_le := λ _ x hx _ ha ↦ ha x hx,
    le_Inf := λ _ _ h _ hb _ hd ↦ h _ hd hb
  }

/-
## Least Fixed Points
-/

namespace Fix

def lfp [CompleteLattice α]
  (f: α → α): α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le [CompleteLattice α] {f: α → α}
  (h: f a ≤ a):
  lfp f ≤ a :=
  CompleteLattice.Inf_le _ h

theorem le_lfp [CompleteLattice α] {f: α → α}
  (h: ∀a', f a' ≤ a' → a ≤ a'):
  a ≤ lfp f :=
  CompleteLattice.le_Inf h

end Fix

/-
## Monotonic Functions
-/

def monotone [PartialOrder α] [PartialOrder β]
  (f: α → β): Prop :=
  ∀a b, a ≤ b → f a ≤ f b

theorem monotone_id [PartialOrder α]:
  monotone (@id α) := λ _ _ ↦ id

theorem monotone_const [PartialOrder α] [PartialOrder β]
  (b: β): monotone (λ _: α ↦ b) :=
  λ _ _ _ ↦ PartialOrder.le_refl b

theorem monotone_union [PartialOrder α]
  (f g: α → Set β) (hf: monotone f) (hg: monotone g):
  monotone (λ a ↦ f a ∪ g a) :=
  λ a a' ha _b hb ↦
    match hb with
    | Or.inl h => Or.inl (hf a a' ha h)
    | Or.inr h => Or.inr (hg a a' ha h)

/-
## The Knaster-Tarski Fixpoint Theorem
-/

namespace Fix

theorem lfp_eq [CompleteLattice α] (f: α → α)
    (hf: monotone f): lfp f = f (lfp f) :=
  let h: f (lfp f) ≤ lfp f :=
    le_lfp (λ a h ↦ PartialOrder.le_trans (hf _ a $ lfp_le h) h)
  PartialOrder.le_antisymm (lfp_le $ hf _ _ h) h

end Fix
