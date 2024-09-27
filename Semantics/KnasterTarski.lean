import Semantics.Set

-- Concrete Semantics with Isabelle
-- 10.4.1 The Knaster-Tarski Fixpoint Theorem on Sets

-- define a partial order
class PartialOrder (α: Type) extends LE α, LT α where
  le_refl: ∀ a: α, a ≤ a
  le_trans: ∀ a b c: α, a ≤ b → b ≤ c → a ≤ c
  le_iff_le_not_le: ∀ a b: α, a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_antisymm: ∀ a b: α, a ≤ b → b ≤ a → a = b

theorem PartialOrder.le_rfl [PartialOrder α] {a: α}: a ≤ a := le_refl a

instance Set.partialOrder: PartialOrder (Set α) :=
  {
    le := fun A B => A ⊆ B,
    lt := fun A B => A ⊆ B ∧ ¬B ⊆ A,
    le_refl := fun _ _ ha => ha,
    le_antisymm := fun _ _ h1 h2 => subset_antisymm h1 h2,
    le_iff_le_not_le := fun _ _ => Iff.rfl,
    le_trans := fun _ _ _ h1 h2 _ ha => h2 (h1 ha)
  }

class CompleteLattice (α: Type) extends PartialOrder α where
  Inf: Set α → α
  Inf_le: ∀ s: Set α, ∀x ∈ s, Inf s ≤ x
  le_Inf: ∀ (s: Set α) (a: α), (∀ b ∈ s, a ≤ b) → a ≤ Inf s

theorem inf_unique {α: Type} [CompleteLattice α] (s: Set α) (a b: α)
  (h: CompleteLattice.Inf s = a) (h': CompleteLattice.Inf s = b): a = b :=
  PartialOrder.le_antisymm _ _ (h ▸ h' ▸ PartialOrder.le_refl b) (h' ▸ h ▸ PartialOrder.le_refl a)

instance Set.completeLattice: CompleteLattice (Set α) :=
  {
    Inf := fun s => {x | ∀ A ∈ s, x ∈ A},
    Inf_le := fun _ x hx _ ha => ha x hx,
    le_Inf := fun _ _ h _ hb _ hd => h _ hd hb
  }

/-
## Least Fixed Points
-/

def lfp {α: Type} [CompleteLattice α] (f: α → α): α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le {α: Type} [CompleteLattice α] {f: α → α}
    {a: α} (h: f a ≤ a):
  lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp {α: Type} [CompleteLattice α] {f: α → α}
    {a: α} (h: ∀a', f a' ≤ a' → a ≤ a'):
  a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

/-
## Monotonic Functions
-/

def monotone {α β: Type} [PartialOrder α] [PartialOrder β]
  (f: α → β): Prop :=
  ∀a b, a ≤ b → f a ≤ f b

theorem monotone_id {α: Type} [PartialOrder α]:
  monotone (fun a: α => a) := fun _ _ h => h

theorem monotone_const {α β: Type} [PartialOrder α]
    [PartialOrder β] (b: β):
  monotone (fun _: α => b) := fun _ _ _ => PartialOrder.le_refl b

theorem monotone_union {α β: Type} [PartialOrder α]
    (f g: α → Set β) (hf: monotone f) (hg: monotone g):
  monotone (fun a => f a ∪ g a) :=
  by
    intro a₁ a₂ ha b hb
    cases hb with
    | inl h => exact Or.inl (hf a₁ a₂ ha h)
    | inr h => exact Or.inr (hg a₁ a₂ ha h)

/-
## The Knaster-Tarski Fixpoint Theorem
-/

theorem lfp_eq {α: Type} [CompleteLattice α] (f: α → α)
    (hf: monotone f): lfp f = f (lfp f) :=
  let h: f (lfp f) ≤ lfp f :=
    le_lfp (fun a h => PartialOrder.le_trans _ _ _ (hf _ a $ lfp_le h) h)
  PartialOrder.le_antisymm _ _ (lfp_le $ hf _ _ h) h
