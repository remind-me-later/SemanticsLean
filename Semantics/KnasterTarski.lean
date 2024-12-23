import Semantics.Set

-- Concrete Semantics with Isabelle
-- 10.4.1 The Knaster-Tarski Fixpoint Theorem on Sets

/-
## Complete lattices
-/

class PartialOrder (α: Type) extends LE α, LT α where
  le_refl: ∀a: α, a <= a
  le_trans: ∀{{a b c: α}}, a <= b -> b <= c -> a <= c
  lt_iff_le_not_le: ∀{{a b: α}}, a < b <-> a <= b ∧ ¬(b <= a)
  le_antisymm: ∀{{a b: α}}, a <= b -> b <= a -> a = b

@[refl]
theorem PartialOrder.le_rfl [PartialOrder α] {a: α}: a <= a := le_refl a

class CompleteLattice (α: Type) extends PartialOrder α where
  Inf: Set α -> α
  Inf_le: ∀{{s: Set α}}, ∀x ∈ s, Inf s <= x
  le_Inf: ∀{{s: Set α}} {{a: α}}, (∀b ∈ s, a <= b) -> a <= Inf s

theorem inf_unique [CompleteLattice α] (s: Set α) (a b: α)
  (h: CompleteLattice.Inf s = a) (h': CompleteLattice.Inf s = b): a = b :=
  PartialOrder.le_antisymm
    (h ▸ h' ▸ PartialOrder.le_rfl)
    (h' ▸ h ▸ PartialOrder.le_rfl)

/-
## Set instances
-/

instance Set.completeLattice: CompleteLattice (Set α) := {
  le := (. ⊆ .),
  lt := (. ⊂ .),
  le_refl := fun _a _b => id,
  le_antisymm := fun _a _b => Subset.antisymm,
  lt_iff_le_not_le := fun _a _b =>
    ⟨fun ⟨hl, hr⟩ => ⟨hl, (hr $ Subset.antisymm hl .)⟩,
      fun ⟨hl, hr⟩ => ⟨hl, (hr $ Subset.from_eq $ Eq.symm .)⟩⟩
  le_trans := fun _a _b _c => Subset.trans
  Inf := fun a => {x | ∀b ∈ a, x ∈ b},
  Inf_le := fun _ x hx _ ha => ha x hx,
  le_Inf := fun _ _ h _ hb _ hd => h _ hd hb
}

/-
## Least Fixed Points
-/

namespace Fix

def pre_fp [PartialOrder α] (f: α -> α) (a: α): Prop :=
  f a <= a

def lfp [CompleteLattice α] (f: α -> α): α :=
  CompleteLattice.Inf {a | f a <= a}

theorem lfp_le [CompleteLattice α] {f: α -> α} (h: pre_fp f a):
  lfp f <= a :=
  CompleteLattice.Inf_le _ h

theorem le_lfp [CompleteLattice α] {f: α -> α}
  (h: ∀a', pre_fp f a' -> a <= a'):
  a <= lfp f :=
  CompleteLattice.le_Inf h

end Fix

/-
## Monotonic Functions
-/

def monotone [PartialOrder α] [PartialOrder β] (f: α -> β): Prop :=
  ∀a b, a <= b -> f a <= f b

theorem monotone_id [PartialOrder α]:
  monotone (@id α) := fun _ _ => id

theorem monotone_const [PartialOrder α] [PartialOrder β]
  (b: β): monotone (fun _: α => b) :=
  fun _ _ _ => PartialOrder.le_refl b

theorem Set.ite_mono (t: Set α) (hab: a ⊆ b) (hab': a' ⊆ b'):
  ite t a a' ⊆ ite t b b' := fun _ hite =>
  match hite with
  | Or.inl ⟨hl, hr⟩ => Or.inl ⟨hab hl, hr⟩
  | Or.inr ⟨hl, hr⟩ => Or.inr ⟨hab' hl, hr⟩

theorem SRel.comp_mono (hfh: f ⊆ h) (hgk: g ⊆ k): f ○ g ⊆ h ○ k :=
  fun _ ⟨z, hl, hr⟩ => ⟨z, hfh hl, hgk hr⟩

/-
## The Knaster-Tarski Fixpoint Theorem
-/

namespace Fix

theorem lfp_eq [CompleteLattice α] (f: α -> α)
    (hf: monotone f): lfp f = f (lfp f) :=
  have h: f (lfp f) <= lfp f :=
    le_lfp (fun a h => PartialOrder.le_trans (hf _ a $ lfp_le h) h)
  PartialOrder.le_antisymm (lfp_le (hf _ _ h)) h

end Fix
