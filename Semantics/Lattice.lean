import Semantics.SetRelation

-- Concrete Semantics with Isabelle
-- 10.4.1 The Knaster-Tarski Fixpoint Theorem on Sets

/-
## Complete lattices
-/

class Preorder (α: Type)  extends LE α, LT α where
  le_refl: ∀a: α, a ≤ a
  le_trans: ∀{{a b c: α}}, a ≤ b → b ≤ c → a ≤ c
  lt_iff_le_not_le: ∀{{a b: α}}, a < b ↔ a ≤ b ∧ ¬(b ≤ a)

@[refl]
theorem Preorder.le_rfl [Preorder α] {a: α}: a ≤ a := Preorder.le_refl a

class PartialOrder (α: Type) extends Preorder α where
  le_antisymm: ∀{{a b: α}}, a ≤ b → b ≤ a → a = b

class CompleteLattice (α: Type) extends PartialOrder α where
  Inf: Set α → α
  Inf_le: ∀{{s: Set α}}, ∀x ∈ s, Inf s ≤ x
  le_Inf: ∀{{s: Set α}} {{a: α}}, (∀b ∈ s, a ≤ b) → a ≤ Inf s

theorem CompleteLattice.Inf_unique [CompleteLattice α] (s: Set α) (a b: α)
  (h: CompleteLattice.Inf s = a) (h': CompleteLattice.Inf s = b): a = b :=
  PartialOrder.le_antisymm (h ▸ h' ▸ Preorder.le_rfl) (h' ▸ h ▸ Preorder.le_rfl)

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
  Inf := fun a => ⋂₀ a,
  Inf_le := fun _ x hx _ ha => ha x hx,
  le_Inf := fun _ _ h _ hb _ hd => h _ hd hb
}

theorem Set.inf_eq (a: Set (Set α)): (⋂₀ a) = CompleteLattice.Inf a := rfl

/-
## Monotonic Functions
-/

def Monotone [Preorder α] [Preorder β] (f: α → β): Prop :=
  ∀a b, a ≤ b → f a ≤ f b

structure OrderHom (α β: Type) [Preorder α] [Preorder β] where
  toFun: α → β
  monotone': Monotone toFun

infixr:25 " →o " => OrderHom

instance OrderHom.coerceFun [Preorder α] [Preorder β]:
  CoeFun (α →o β) (fun _ => α → β) := ⟨fun f => f.toFun⟩

instance OrderHom.id [Preorder α]: α →o α := {
  toFun := fun x => x,
  monotone' := fun _ _ h => h
}

instance OrderHom.const [Preorder α] [Preorder β]: Coe (β) (α →o β) :=
⟨fun b => {
    toFun := fun _ => b,
    monotone' := fun _ _ _ => Preorder.le_refl b
}⟩

theorem Set.ite_mono (t: Set α) (hab: a ⊆ b) (hab': a' ⊆ b'):
  ite t a a' ⊆ ite t b b' := fun _ hite =>
  match hite with
  | .inl ⟨hl, hr⟩ => .inl ⟨hab hl, hr⟩
  | .inr ⟨hl, hr⟩ => .inr ⟨hab' hl, hr⟩

theorem SRel.comp_mono (hfh: f ⊆ h) (hgk: g ⊆ k): f ○ g ⊆ h ○ k :=
  fun _ ⟨z, hl, hr⟩ => ⟨z, hfh hl, hgk hr⟩

/-
## Least Fixed Points
-/

-- pre-fixed point
def OrderHom.pfp [CompleteLattice α] (f: α →o α) (a: α): Prop :=
  f a ≤ a

theorem OrderHom.pfp_eq [CompleteLattice α] (f: α →o α) (a: α):
  OrderHom.pfp f a = (f a ≤ a) := rfl

def OrderHom.lfp [CompleteLattice α] (f: α →o α): α :=
  CompleteLattice.Inf {a | pfp f a}

theorem OrderHom.lfp_le [CompleteLattice α] {f: α →o α} (h: pfp f a):
  lfp f ≤ a :=
  CompleteLattice.Inf_le _ h

theorem OrderHom.le_lfp [CompleteLattice α] {f: α →o α}
  (h: ∀a', pfp f a' → a ≤ a'):
  a ≤ lfp f :=
  CompleteLattice.le_Inf h

/-
## The Knaster-Tarski Fixpoint Theorem
-/

theorem OrderHom.lfp_eq [CompleteLattice α] (f: α →o α):
  lfp f = f (lfp f) :=
  have h: f (lfp f) ≤ lfp f :=
    le_lfp (fun a h => Preorder.le_trans (f.monotone' _ a $ lfp_le h) h)
  PartialOrder.le_antisymm (lfp_le (f.monotone' _ _ h)) h
