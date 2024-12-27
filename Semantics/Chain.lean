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
      mp := fun ⟨i, hi⟩ => match i with | .zero => .inl hi | .succ _ => .inr hi,
      mpr := fun hx => match hx with | .inl hx => ⟨0, hx⟩ | .inr hx => ⟨1, hx⟩
    }
  have hh := hset ▸ hset' ▸ (h _ hchain)

  exact hh ▸ .inl hx

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

theorem fpow.succ_eq (f: α → α): fpow f (n + 1) x = f (fpow f n x) := rfl

theorem fpow.isChain (f: Set α →o Set α): isωChain (fun i => fpow f i ∅) := by
  intro i
  induction i with
  | zero => exact fun x hx => absurd hx (Set.mem_empty x)
  | succ _ ih => exact f.monotone' _ _ ih

instance fpow.ωChain (f: Set α →o Set α): ωChain α where
  toSeq := fun i => fpow f i ∅
  chain' := fpow.isChain f

theorem fpow.succ_limit_eq (f: Set α →o Set α):
  (⋃ i, fpow f (i + 1) ∅) = (⋃ i, fpow f i ∅) := Set.ext fun _ => {
    mp := fun ⟨i, hi⟩ => match i with
      | .zero => ⟨1, hi⟩ | .succ i => ⟨i+1+1, hi⟩,
    mpr := fun ⟨i, hi⟩ => match i with
      | .zero => absurd hi (Set.mem_empty _) | .succ i => ⟨i, hi⟩
  }

def ωContinuousHom.lfp (f: α →ω α): Set α := ⋃ i, fpow f i ∅

theorem kleene_fix {f: α →ω α}: f.toOrderHom.lfp = f.lfp := by
  apply Subset.antisymm
  . have hpfp: f.toOrderHom.pfp (⋃ i, (fpow f i) ∅) := fun _ ha =>
      have hcont := f.continuous' _ (fpow.isChain f.toOrderHom)
      fpow.succ_limit_eq _ ▸ hcont ▸ ha
    exact OrderHom.lfp_le hpfp

  . intro a ⟨i, ha⟩
    revert a ha
    induction i with
    | zero => exact fun a ha => absurd ha (Set.mem_empty a)
    | succ i ih =>
      have hmono := fpow.succ_eq f ▸ f.monotone' _ _ ih
      exact f.toOrderHom.lfp_eq ▸ hmono
