import Semantics.Set
import Semantics.KnasterTarski

def Chain {α: Type} (S: Nat → Set α): Prop :=
  ∀i, S i ⊆ S (i + 1)

def continuous {α β: Type} (f: Set α → Set β): Prop :=
  ∀S, Chain S → f (⋃ i, S i) = ⋃ i, f (S i)

theorem continuous_mono {f: Set α → Set α} (h: continuous f):
  monotone f := by
  intro a b hab _ hx

  have hchain: Chain (fun i => if i = 0 then a else b) := fun i x =>
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

def fexp {α: Type} (f: α → α) (n: Nat): α → α
  | a => match n with
    | .zero => a
    | .succ n => f (fexp f n a)

theorem fexp_next (f: α → α) (x: α): (fexp f (n + 1)) x = f ((fexp f n) x) := by
  induction n <;> rfl

theorem fexp_chain (hmono: monotone f): Chain (fun i => fexp f i {}) := by {
  intro i
  simp at *
  induction i with
  | zero =>
    unfold fexp
    simp [Membership.mem, Set.Mem, EmptyCollection.emptyCollection]
    intro x hx
    contradiction
  | succ i ih =>
    unfold fexp
    simp at *
    unfold monotone at hmono
    exact hmono _ _ ih
}

theorem kleene_fix {f: Set α → Set α} (h: continuous f):
  Fix.lfp f = ⋃ i, (fexp f i) {} := by {
  apply Subset.antisymm
  . suffices Fix.pre_fp f (⋃ i, (fexp f i) {}) by exact Fix.lfp_le this

    intro a ha

    specialize h _ (fexp_chain (continuous_mono h))
    simp [←fexp_next f {}] at h

    have hh: (Set.iUnion fun i => fexp f (i + 1) ∅) = (Set.iUnion fun i => fexp f i ∅) := by {
      simp [Set.iUnion]
      apply Set.ext
      intro x
      constructor
      . intro ⟨i, hi⟩
        cases i with
        | zero =>
          exact ⟨1, hi⟩
        | succ i =>
          exact ⟨i+1+1, hi⟩
      . intro ⟨i, hi⟩
        cases i with
        | zero =>
          exists 0
        | succ i =>
          exists i
    }

    rw [hh] at h
    rw [h] at ha

    exact ha
  .
    intro a ⟨i, ha⟩
    revert a ha
    rw [←Set.Subset]
    simp at *
    induction i with
    | zero =>
      unfold fexp
      simp
      intro a ha
      contradiction
    | succ i ih =>
      have hmono := continuous_mono h
      unfold monotone at hmono
      specialize hmono _ _ ih
      rw [←fexp_next f {}] at hmono
      rw [Fix.lfp_eq f (continuous_mono h)]
      exact hmono
}
