import Mathlib.Data.Set.Defs

/-
  # Set theorems
-/

theorem Set.mem_empty {α : Type} (a : α) :
  a ∈ (∅ : Set α) ↔ False := by
  simp only [Membership.mem, Set.Mem, EmptyCollection.emptyCollection]

theorem Set.empty_of_false_prop {α : Type} :
  {a | False} = (∅ : Set α) := rfl

theorem Set.subseteq_def {α : Type} (A B : Set α) :
  A ⊆ B ↔ ∀a, a ∈ A → a ∈ B := Iff.rfl

theorem Set.mem_singleton {α : Type} (a b : α) :
  a ∈ ({b} : Set α) ↔ a = b := Iff.rfl

theorem Set.mem_self {α : Type} (A : Set α) :
  {a | a ∈ A} = A := rfl

theorem Set.mem_comprehend {α : Type} (a : α) (P : α → Prop) :
  a ∈ ({a | P a} : Set α) ↔ P a := Iff.rfl

theorem Set.empty_union {α : Type} (A : Set α) :
  ∅ ∪ A = A := by
  simp only [Set.mem_empty, Set.mem_self, Union.union, Set.union, false_or]

theorem Set.union_empty {α : Type} (A : Set α) :
  A ∪ ∅ = A :=
  by simp only [Set.mem_empty, Set.mem_self, Union.union, Set.union, or_false]

theorem Set.mem_union {α : Type} (a : α) (A B : Set α) :
  a ∈ A ∪ B ↔ a ∈ A ∨ a ∈ B := Iff.rfl

theorem Set.mem_diff.{u} {α : Type u} {s t : Set α} (x : α) :
  x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Iff.rfl

/-
  ### Basic subset properties
-/

theorem subset_refl {α : Type} (x : Set α) : x ⊆ x := fun _ => id

theorem subset_trans {α : Type} {x y z : Set α} (h1 : x ⊆ y) (h2 : y ⊆ z) : x ⊆ z :=
  fun _ h => h2 (h1 h)

theorem subset_antisymm {α : Type} {x y : Set α} (h1 : x ⊆ y) (h2 : y ⊆ x) : x = y :=
  funext fun _ => propext ⟨fun h => h1 h, fun h => h2 h⟩

theorem subset_from_eq {α : Type} {x y : Set α} (h : x = y) : x ⊆ y :=
  fun _ h1 => h ▸ h1

/-
  ### Set if then else
-/

protected def Set.ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t


theorem Set.ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') :
    t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  fun _ h2 =>
    match h2 with
    | Or.inl h3 => Or.inl ⟨h h3.1, h3.2⟩
    | Or.inr h3 => Or.inr ⟨h' h3.1, h3.2⟩

/-
  ### Set Relations
-/

namespace SRel

notation:20 α " →ᵍ " β => Set (α × β)

def id: α →ᵍ α := {p | p.1 = p.2}

theorem mem_id:
  (a, b) ∈ @id α ↔ a = b := Iff.rfl

def comp (f g: α →ᵍ α): α →ᵍ α :=
  {x | ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g}

infixl:90 " ○ " => SRel.comp

theorem mem_comp {f g: α →ᵍ α}:
  x ∈ f ○ g ↔ ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g := Iff.rfl

theorem comp_mono {α: Type} {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k): f ○ g ⊆ h ○ k :=
  fun _ ⟨z, h, h'⟩ => ⟨z, h₁ h, h₂ h'⟩

theorem comp_id_right {f: α →ᵍ α}:
  f ○ id = f := by
  funext x
  simp only [eq_iff_iff]
  apply Iff.intro
  . intro h
    simp only [comp, Membership.mem, Set.Mem] at h
    cases h with
    | intro z h =>
      cases h with
      | intro hl hr =>
        cases hr with
        | refl => exact hl
  . intro h
    simp only [comp, Membership.mem, Set.Mem]
    exact ⟨x.2, ⟨h, rfl⟩⟩

theorem comp_id_left {f: α →ᵍ α}:
  id ○ f = f := by
  funext x
  simp only [eq_iff_iff]
  apply Iff.intro
  . intro h
    simp only [comp, Membership.mem, Set.Mem] at h
    cases h with
    | intro z h =>
      cases h with
      | intro hl hr =>
        cases hl with
        | refl => exact hr
  . intro h
    simp only [comp, Membership.mem, Set.Mem]
    exact ⟨x.1, ⟨rfl, h⟩⟩

end SRel
