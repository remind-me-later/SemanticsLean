-- # Sets

def Set (α: Type) := α → Prop

def setOf (p: α → Prop): Set α := p

namespace Set

protected def Mem (s: Set α) (a: α): Prop := s a

instance: Membership α (Set α) := ⟨Set.Mem⟩

theorem ext {a b: Set α} (h: ∀(x: α), x ∈ a ↔ x ∈ b): a = b :=
  funext fun x => propext (h x)

protected def Subset (a b: Set α) :=
  ∀{{x}}, x ∈ a → x ∈ b

instance: HasSubset (Set α) := ⟨Set.Subset⟩

protected def SSubset (a b: Set α) := a ⊆ b ∧ a ≠ b

instance: HasSSubset (Set α) := ⟨Set.SSubset⟩

instance: EmptyCollection (Set α) := ⟨fun _ => False⟩

theorem mem_empty (a: α): a ∉ (∅: Set α) := id

notation (priority := high) "{" x " | " p "}" => setOf fun x => p

theorem mem_comprehend (a: α) (P: α → Prop): a ∈ ({a | P a}: Set α) ↔ P a :=
  Iff.rfl

def univ: Set α := {_ | True}

theorem mem_univ (a: α): a ∈ univ := trivial

theorem univ_def {α: Type}: @univ α = {_ | True} := rfl

protected def insert (a: α) (s: Set α): Set α := {x | x = a ∨ x ∈ s}

instance: Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a: α): Set α := {b | b = a}

instance instSingletonSet: Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (a b: Set α): Set α := {x | x ∈ a ∨ x ∈ b}

instance: Union (Set α) := ⟨Set.union⟩

theorem mem_union {s t: Set α} (x: α): x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl

theorem union_empty (a: Set α): a ∪ ∅ = a := by
  apply ext
  intro x
  simp [mem_union, mem_comprehend]
  intro h
  contradiction

protected def inter (a b: Set α): Set α := {x | x ∈ a ∧ x ∈ b}

instance: Inter (Set α) := ⟨Set.inter⟩

theorem mem_inter {s t: Set α} (x: α): x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl

theorem inter_univ (a: Set α): a ∩ univ = a := by
  apply ext
  intro x
  simp [mem_inter, mem_comprehend]
  intro h
  exact mem_univ x

protected def compl (s: Set α): Set α := {a | a ∉ s}

protected def diff (a b: Set α): Set α := {x | x ∈ a ∧ x ∉ b}

instance: SDiff (Set α) := ⟨Set.diff⟩

theorem mem_diff {s t: Set α} (x: α): x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

theorem diff_univ (a: Set α): a \ univ = ∅ := by
  apply ext
  intro x
  simp [mem_diff, mem_comprehend]
  constructor
  . intro ⟨ha, hu⟩
    exact absurd (mem_univ x) hu
  . intro h
    contradiction

def ite (t a b: Set α): Set α := a ∩ t ∪ b \ t

def iUnion {α: Type} (S: Nat → Set α): Set α :=
  {a | ∃i, a ∈ S i}

notation "⋃" i ", " S => (iUnion fun i => S)

def sUnion {α: Type} (S: Set (Set α)): Set α :=
  {a | ∃B ∈ S, a ∈ B}

notation "⋃₀ " S => sUnion S

def iInter {α: Type} (S: Nat → Set α): Set α :=
  {a | ∀i, a ∈ S i}

notation "⋂" i ", " S => (iInter fun i => S)

def sInter {α: Type} (S: Set (Set α)): Set α :=
  {a | ∀B ∈ S, a ∈ B}

notation "⋂₀ " S => sInter S

theorem mem_sInter {α: Type} {S: Set (Set α)} {a: α}: a ∈ (⋂₀ S) ↔ ∀B ∈ S, a ∈ B :=
  Iff.rfl

theorem sInter_univ {α: Type}: (⋂₀ (@univ $ Set α)) = ∅ := by
  apply ext
  intro x
  simp [mem_sInter, mem_comprehend]
  constructor
  . intro h
    specialize h ∅
    apply h
    trivial
  . intro h B hB
    contradiction

end Set

namespace Subset

@[refl]
theorem refl (x: Set α): x ⊆ x := fun _ => id

theorem trans {a b c: Set α} (hab: a ⊆ b) (hbc: b ⊆ c): a ⊆ c :=
  fun _ h => hbc (hab h)

theorem antisymm {a b: Set α} (hab: a ⊆ b) (hba: b ⊆ a): a = b :=
  funext fun _ => propext ⟨(hab .), (hba .)⟩

theorem from_eq {a b: Set α} (heq: a = b): a ⊆ b :=
  fun _x hxa => heq ▸ hxa

end Subset
