import Mathlib.Data.Set.Defs

/-
  # Set theorems
-/

@[simp] theorem Set.Mem_empty {α : Type} (a : α) :
  a ∈ (∅ : Set α) ↔ False :=
  by simp [Membership.mem, Set.Mem, EmptyCollection.emptyCollection]

@[simp] theorem Set.compreh_False {α : Type} :
  {a | False} = (∅ : Set α) :=
  by rfl

@[simp] theorem Set.subseteq_def {α : Type} (A B : Set α) :
  A ⊆ B ↔ ∀a, a ∈ A → a ∈ B :=
  by rfl

@[simp] theorem Set.Mem_singleton {α : Type} (a b : α) :
  a ∈ ({b} : Set α) ↔ a = b :=
  by rfl

@[simp] theorem Set.Mem_compreh {α : Type} (A : Set α) :
  {a | a ∈ A} = A :=
  by rfl

@[simp] theorem Set.compreh_Mem {α : Type} (a : α) (P : α → Prop) :
  a ∈ ({a | P a} : Set α) ↔ P a :=
  by rfl

@[simp] theorem Set.empty_union {α : Type} (A : Set α) :
  ∅ ∪ A = A :=
  by simp [Union.union, Set.union]

@[simp] theorem Set.union_empty {α : Type} (A : Set α) :
  A ∪ ∅ = A :=
  by simp [Union.union, Set.union]

@[simp] theorem Set.Mem_union {α : Type} (a : α) (A B : Set α) :
  a ∈ A ∪ B ↔ a ∈ A ∨ a ∈ B :=
  by rfl


/-
  ### Basic subset properties
-/

theorem subset_refl {α : Type} (x : Set α) : x ⊆ x := fun _ => id

theorem subset_trans {α : Type} {x y z : Set α} (h1 : x ⊆ y) (h2 : y ⊆ z) : x ⊆ z :=
  fun _ h => h2 (h1 h)

theorem subset_antisymm {α : Type} {x y : Set α} (h1 : x ⊆ y) (h2 : y ⊆ x) : x = y :=
  funext fun _ => propext ⟨fun h => h1 h, fun h => h2 h⟩

theorem subset_from_eq {α : Type} {x y : Set α} (h : x = y) : x ⊆ y :=
  fun _ h' => h ▸ h'

/-
  ### Set if then else
-/

protected def Set.ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t

@[simp]
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

@[simp]
theorem mem_id:
  (a, b) ∈ @id α ↔ a = b := Iff.rfl

def comp (f g: α →ᵍ α): α →ᵍ α :=
  {x | ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g}

infixl:90 " ○ " => SRel.comp

@[simp]
theorem mem_comp {f g: α →ᵍ α}:
  x ∈ f ○ g ↔ ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g := Iff.rfl

@[simp]
theorem comp_mono {α: Type} {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k): f ○ g ⊆ h ○ k :=
  fun _ ⟨z, h, h'⟩ => ⟨z, h₁ h, h₂ h'⟩

@[simp]
theorem comp_id_right {f: α →ᵍ α}: f ○ id = f :=
  by
    sorry

@[simp]
theorem comp_id_left {f: α →ᵍ α}:
  id ○ f = f := by
  sorry

end SRel
