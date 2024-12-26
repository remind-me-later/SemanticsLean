import Semantics.Set
import Semantics.Lattice

def isωChain {α: Type} (s: Nat → Set α): Prop :=
  ∀i, s i ⊆ s (i + 1)

structure ωChain (α: Type) where
  toSeq: Nat → Set α
  chain': isωChain toSeq

def ωContinuous {α β: Type} (f: Set α → Set β): Prop :=
  ∀s, isωChain s → f (⋃ i, s i) = ⋃ i, f (s i)

theorem ωContinuous.isMono (f: Set α → Set β) (h: ωContinuous f):
  Monotone f := by
  intro a b hab _ hx

  have hchain: isωChain (fun i => if i = 0 then a else b) := fun i x =>
    match i with | .zero => (hab .) | .succ j => (.)
  have hset: (⋃ i, if i = 0 then a else b) = b := Set.ext fun _ => {
      mp := fun ⟨i, hi⟩ => match i with | .zero => hab hi | .succ _ => hi,
      mpr := (⟨1, .⟩)
    }
  have hset': (⋃ i, f (if i = 0 then a else b)) = (f a ∪ f b) :=
    Set.ext fun _ => {
      mp := fun ⟨i, hi⟩ => match i with
        | .zero => Or.inl hi
        | .succ _ => Or.inr hi,
      mpr := fun hx => match hx with
        | .inl hx => ⟨0, hx⟩
        | .inr hx => ⟨1, hx⟩
    }
  have hh := hset ▸ hset' ▸ (h _ hchain)

  exact hh ▸ Or.inl hx

structure ωContinuousHom (α β: Type) extends Set α →o Set β where
  continuous': ωContinuous toFun
  monotone' := ωContinuous.isMono toFun continuous'

infixr:25 " →ω " => ωContinuousHom

instance ωContinuousHom.coerceFun {α β: Type}:
  CoeFun (α →ω β) (fun _ => Set α → Set β) := ⟨fun f => f.toFun⟩

def fpow {α: Type} (f: α → α) (n: Nat): α → α
  | a => match n with
    | .zero => a
    | .succ n => f (fpow f n a)

theorem fpow_succ (f: α → α) (x: α): (fpow f (n + 1)) x = f (fpow f n x) := by
  induction n <;> rfl

theorem fpow_chain (f: Set α →o Set α): isωChain (fun i => fpow f i ∅) := by {
  intro i
  simp at *
  induction i with
  | zero =>
    unfold fpow
    simp [Membership.mem, Set.Mem, EmptyCollection.emptyCollection]
    intro x hx
    contradiction
  | succ i ih =>
    unfold fpow
    simp at *
    exact f.monotone' _ _ ih
}

instance (f: Set α →o Set α): ωChain α where
  toSeq := fun i => fpow f i ∅
  chain' := fpow_chain f

def ωContinuousHom.lfp (f: α →ω α): Set α := ⋃ i, fpow f i ∅

theorem kleene_fix {f: α →ω α}:
  f.toOrderHom.lfp = f.lfp := by {
  apply Subset.antisymm
  . suffices f.toOrderHom.pfp (⋃ i, (fpow f i) ∅) by exact OrderHom.lfp_le this

    intro a ha

    have h := f.continuous' _ (fpow_chain f.toOrderHom)
    simp [←fpow_succ f ∅] at h

    have hh: (Set.iUnion fun i => fpow f (i + 1) ∅) = (Set.iUnion fun i => fpow f i ∅) := Set.ext fun x => {
      mp := fun ⟨i, hi⟩ => match i with
        | .zero => ⟨1, hi⟩
        | .succ i => ⟨i+1+1, hi⟩,
      mpr := fun ⟨i, hi⟩ => match i with
        | .zero => by contradiction
        | .succ i => ⟨i, hi⟩
    }

    rw [hh] at h
    rw [h] at ha

    exact ha

  . intro a ⟨i, ha⟩
    revert a ha
    rw [←Set.Subset]
    simp at *
    induction i with
    | zero =>
      unfold fpow
      simp
      intro a ha
      contradiction
    | succ i ih =>
      have hmono := f.monotone' _ _ ih
      rw [←fpow_succ f ∅] at hmono
      rw [f.toOrderHom.lfp_eq]
      exact hmono
}
