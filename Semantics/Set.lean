-- # Sets

def Set (α: Type) := α -> Prop

def setOf (p: α -> Prop): Set α := p

namespace Set

protected def Mem (s: Set α) (a: α): Prop := s a

instance: Membership α (Set α) := ⟨Set.Mem⟩

theorem ext {a b: Set α} (h: ∀(x: α), x ∈ a <-> x ∈ b): a = b :=
  funext fun x => propext (h x)

protected def Subset (a b: Set α) :=
  ∀{{x}}, x ∈ a -> x ∈ b

instance: HasSubset (Set α) := ⟨Set.Subset⟩

protected def SSubset (a b: Set α) := a ⊆ b ∧ a ≠ b

instance: HasSSubset (Set α) := ⟨Set.SSubset⟩

instance: EmptyCollection (Set α) := ⟨fun _ => False⟩

notation (priority := high) "{" x " | " p "}" => setOf fun x => p

def univ: Set α := {_ | True}

protected def insert (a: α) (s: Set α): Set α := {x | x = a ∨ x ∈ s}

instance: Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a: α): Set α := {b | b = a}

instance instSingletonSet: Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (a b: Set α): Set α := {x | x ∈ a ∨ x ∈ b}

instance: Union (Set α) := ⟨Set.union⟩

protected def inter (a b: Set α): Set α := {x | x ∈ a ∧ x ∈ b}

instance: Inter (Set α) := ⟨Set.inter⟩

protected def compl (s: Set α): Set α := {a | a ∉ s}

protected def diff (a b: Set α): Set α := {x | x ∈ a ∧ x ∉ b}

instance: SDiff (Set α) := ⟨Set.diff⟩

end Set

/-
  ## Set theorems
-/

theorem Set.mem_comprehend (a: α) (P: α -> Prop): a ∈ ({a | P a}: Set α) <-> P a :=
  Iff.rfl

theorem Set.mem_diff {s t: Set α} (x: α): x ∈ s \ t <-> x ∈ s ∧ x ∉ t :=
  Iff.rfl

/-
  ### Basic subset properties
-/

theorem Subset.refl (x: Set α): x ⊆ x := fun _ => id

theorem Subset.trans {a b c: Set α} (hab: a ⊆ b) (hbc: b ⊆ c): a ⊆ c :=
  fun _ h => hbc (hab h)

theorem Subset.antisymm {a b: Set α} (hab: a ⊆ b) (hba: b ⊆ a): a = b :=
  funext fun _ => propext ⟨(hab .), (hba .)⟩

theorem Subset.from_eq {a b: Set α} (heq: a = b): a ⊆ b :=
  fun _x hxa => heq ▸ hxa

/-
  ### Set if then else
-/

def Set.ite (t a b: Set α): Set α := a ∩ t ∪ b \ t

/-
  ## Set theoretic (partial) functions

  Really these are just relations, but we can think of them as functions
-/

namespace SRel

notation:20 α " ->s " β => Set (α × β)

def id: α ->s α := {p | p.1 = p.2}

theorem mem_id: (a, b) ∈ id <-> a = b :=
  Iff.rfl

def comp (f g: α ->s α): α ->s α :=
  {(x, z) | ∃y, (x, y) ∈ f ∧ (y, z) ∈ g}

infixl:90 " ○ " => SRel.comp

theorem mem_comp: x ∈ f ○ g <-> ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g :=
  Iff.rfl

theorem comp_id: f ○ id = f := by
  apply funext
  intro x
  apply propext
  constructor
  . intro ⟨_, hl, hr⟩
    have := mem_id.mp hr ▸ hl
    exact this
  . exact (⟨_, ., mem_id.mpr rfl⟩)

theorem id_comp: id ○ f = f := by
  apply funext
  intro x
  apply propext
  constructor
  . intro ⟨_, hl, hr⟩
    have := mem_id.mp hl ▸ hr
    exact this
  . exact (⟨_, mem_id.mpr rfl, .⟩)

end SRel
