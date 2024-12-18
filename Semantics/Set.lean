-- # Sets

def Set (α: Type) := α -> Prop

def setOf (p: α -> Prop): Set α := p

namespace Set

protected def Mem (s: Set α) (a: α): Prop := s a

instance: Membership α (Set α) := Membership.mk Set.Mem

theorem ext {a b: Set α} (h: ∀(x: α), x ∈ a <-> x ∈ b): a = b :=
  funext fun x => propext (h x)

protected def Subset (a b: Set α) :=
  ∀{{x}}, x ∈ a -> x ∈ b

instance: LE (Set α) := LE.mk Set.Subset

instance: HasSubset (Set α) := HasSubset.mk (. <= .)

instance: EmptyCollection (Set α) := EmptyCollection.mk fun _ => False

notation (priority := high) "{" x " | " p "}" => setOf fun x => p

def univ: Set α := {_ | True}

protected def insert (a: α) (s: Set α): Set α := {x | x = a ∨ x ∈ s}

instance: Insert α (Set α) := Insert.mk Set.insert

protected def singleton (a: α): Set α := {b | b = a}

instance instSingletonSet: Singleton α (Set α) := Singleton.mk Set.singleton

protected def union (a b: Set α): Set α := {x | x ∈ a ∨ x ∈ b}

instance: Union (Set α) := Union.mk Set.union

protected def inter (a b: Set α): Set α := {x | x ∈ a ∧ x ∈ b}

instance: Inter (Set α) := Inter.mk Set.inter

protected def compl (s: Set α): Set α := {a | a ∉ s}

protected def diff (a b: Set α): Set α := {x | x ∈ a ∧ x ∉ b}

instance: SDiff (Set α) := SDiff.mk Set.diff

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
  funext fun _ => propext (Iff.intro (fun mp => hab mp) (fun mp => hba mp))

theorem Subset.from_eq {a b: Set α} (heq: a = b): a ⊆ b :=
  fun _x hxa => heq ▸ hxa

/-
  ### Set if then else
-/

def Set.ite (t a b: Set α): Set α := a ∩ t ∪ b \ t

theorem Set.ite_mono (t: Set α) (hab: a ⊆ b) (hab': a' ⊆ b'):
  ite t a a' ⊆ ite t b b' := fun _ h2 =>
  match h2 with
  | Or.inl (And.intro hl hr) => Or.inl (And.intro (hab hl) hr)
  | Or.inr (And.intro hl hr) => Or.inr (And.intro (hab' hl) hr)

/-
  ## Set theoretic (partial) functions

  Really these are just relations, but we can think of them as functions
-/

namespace SFun

notation:20 α " ->s " β => Set (α × β)

def id: α ->s α := {p | p.1 = p.2}

theorem mem_id: (a, b) ∈ id <-> a = b :=
  Iff.rfl

def comp (f g: α ->s α): α ->s α :=
  {x | ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g}

infixl:90 " ○ " => SFun.comp

theorem mem_comp: x ∈ f ○ g <-> ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g :=
  Iff.rfl

theorem comp_mono (hfh: f ⊆ h) (hgk: g ⊆ k): f ○ g ⊆ h ○ k :=
  fun _ (Exists.intro z (And.intro hl hr)) =>
    Exists.intro z (And.intro (hfh hl) (hgk hr))

theorem comp_id: f ○ id = f := by
  apply funext
  intro (_x, y)
  apply propext
  constructor
  . intro (Exists.intro z (And.intro hl hr))
    apply mem_id.mp hr ▸ hl
  . exact fun mp => (Exists.intro y (And.intro mp rfl))

theorem id_comp: id ○ f = f := by
  funext (x, _y)
  apply propext
  constructor
  . intro (Exists.intro z (And.intro hl hr))
    apply mem_id.mp hl ▸ hr
  . exact fun mp => (Exists.intro x (And.intro rfl mp))

end SFun
