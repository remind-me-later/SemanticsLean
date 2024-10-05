-- # Sets

def Set (α : Type u) := α → Prop

/-- Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}` -/
def setOf {α : Type u} (p : α → Prop) : Set α :=
  p

namespace Set

/-- Membership in a set -/
protected def Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x ↦ propext (h x))


/-- The subset relation on sets. `s ⊆ t` means that all elements of `s` are elements of `t`.

Note that you should **not** use this definition directly, but instead write `s ⊆ t`. -/
protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

/-- Porting note: we introduce `≤` before `⊆` to help the unifier when applying lattice theorems
to subset hypotheses. -/
instance : LE (Set α) :=
  ⟨Set.Subset⟩

instance : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩

instance : EmptyCollection (Set α) :=
  ⟨fun _ ↦ False⟩

notation "{" x " | " p "}" => setOf (λ x => p)


/-- The universal set on a type `α` is the set containing all elements of `α`.

This is conceptually the "same as" `α` (in set theory, it is actually the same), but type theory
makes the distinction that `α` is a type while `Set.univ` is a term of type `Set α`. `Set.univ` can
itself be coerced to a type `↥Set.univ` which is in bijection with (but distinct from) `α`. -/
def univ : Set α := {_a | True}

/-- `Set.insert a s` is the set `{a} ∪ s`.

Note that you should **not** use this definition directly, but instead write `insert a s` (which is
mediated by the `Insert` typeclass). -/
protected def insert (a : α) (s : Set α) : Set α := {b | b = a ∨ b ∈ s}

instance : Insert α (Set α) := ⟨Set.insert⟩

/-- The singleton of an element `a` is the set with `a` as a single element.

Note that you should **not** use this definition directly, but instead write `{a}`. -/
protected def singleton (a : α) : Set α := {b | b = a}

instance instSingletonSet : Singleton α (Set α) := ⟨Set.singleton⟩

/-- The union of two sets `s` and `t` is the set of elements contained in either `s` or `t`.

Note that you should **not** use this definition directly, but instead write `s ∪ t`. -/
protected def union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}

instance : Union (Set α) := ⟨Set.union⟩

/-- The intersection of two sets `s` and `t` is the set of elements contained in both `s` and `t`.

Note that you should **not** use this definition directly, but instead write `s ∩ t`. -/
protected def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}

instance : Inter (Set α) := ⟨Set.inter⟩

/-- The complement of a set `s` is the set of elements not contained in `s`.

Note that you should **not** use this definition directly, but instead write `sᶜ`. -/
protected def compl (s : Set α) : Set α := {a | a ∉ s}


/-- The difference of two sets `s` and `t` is the set of elements contained in `s` but not in `t`.

Note that you should **not** use this definition directly, but instead write `s \ t`. -/
protected def diff (s t : Set α) : Set α :=
  λ a => a ∈ s ∧ a ∉ t

instance : SDiff (Set α) := ⟨Set.diff⟩

end Set

/-
  ## Set theorems
-/

theorem Set.mem_comprehend {α : Type}
  (a : α) (P : α → Prop):
  a ∈ ({a | P a} : Set α) ↔ P a :=
  Iff.rfl

theorem Set.mem_diff {α : Type u} {s t : Set α}
  (x : α): x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

/-
  ### Basic subset properties
-/

theorem Subset.refl {α : Type}
  (x : Set α): x ⊆ x :=
  λ _ => id

theorem Subset.trans {α : Type} {x y z : Set α}
  (h1 : x ⊆ y) (h2 : y ⊆ z) : x ⊆ z :=
  λ _ h => h2 $ h1 h

theorem Subset.antisymm {α : Type} {x y : Set α}
  (h1 : x ⊆ y) (h2 : y ⊆ x) : x = y :=
  funext λ _ => propext ⟨(h1 ·), (h2 ·)⟩

theorem Subset.from_eq {α : Type} {x y : Set α}
  (h : x = y) : x ⊆ y :=
  λ _ h1 => h ▸ h1

/-
  ### Set if then else
-/

def Set.ite (t s s' : Set α): Set α :=
  s ∩ t ∪ s' \ t

theorem Set.ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α}
  (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂'):
  t.ite s₁ s₁' ⊆ t.ite s₂ s₂' := λ _ h2 =>
  match h2 with
  | Or.inl ⟨hl, hr⟩ => Or.inl ⟨h hl, hr⟩
  | Or.inr ⟨hl, hr⟩ => Or.inr ⟨h' hl, hr⟩

/-
  ## Set theoretic (partial) functions

  Really these are just relations, but we can think of them as functions
-/

namespace SFun

notation:20 α " →ˢ " β => Set (α × β)

def id: α →ˢ α := {p | p.1 = p.2}

theorem mem_id: (a, b) ∈ id ↔ a = b :=
  Iff.rfl

def comp (f g: α →ˢ α): α →ˢ α :=
  {x | ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g}

infixl:90 " ○ " => SFun.comp

theorem mem_comp {f g: α →ˢ α}:
  x ∈ f ○ g ↔ ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g :=
  Iff.rfl

theorem comp_mono {α: Type} {f g h k : Set (α × α)}
  (hfh : f ⊆ h) (hgk : g ⊆ k): f ○ g ⊆ h ○ k :=
  λ _ ⟨z, h, h'⟩ => ⟨z, hfh h, hgk h'⟩

theorem comp_id {f: α →ˢ α}: f ○ id = f := by
  funext x
  apply eq_iff_iff.mpr
  unfold comp
  constructor
  . intro ⟨z, h1, h2⟩
    apply mem_id.mp h2 ▸ h1
  . intro h
    exact ⟨x.2, h, rfl⟩

theorem id_comp {f: α →ˢ α}: id ○ f = f := by
  funext x
  apply eq_iff_iff.mpr
  unfold comp
  constructor
  . intro ⟨z, h1, h2⟩
    apply mem_id.mp h1 ▸ h2
  . intro h
    exact ⟨x.1, rfl, h⟩

end SFun
