-- Our only dependency on mathlib
import Mathlib.Data.Set.Defs

/-
  # Set theorems
-/

theorem Set.mem_comprehend {α : Type} (a : α) (P : α → Prop) :
  a ∈ ({a | P a} : Set α) ↔ P a := Iff.rfl

theorem Set.mem_diff {α : Type u} {s t : Set α} (x : α) :
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

theorem comp_mono {α: Type} {f g h k : Set (α × α)}
  (h₁ : f ⊆ h) (h₂ : g ⊆ k): f ○ g ⊆ h ○ k :=
  fun _ ⟨z, h, h'⟩ => ⟨z, h₁ h, h₂ h'⟩

theorem comp_id_right {f: α →ᵍ α}:
  f ○ id = f := by
  funext x
  apply eq_iff_iff.mpr
  apply Iff.intro
  . intro h
    unfold comp at h
    match h with
    | Exists.intro z h =>
      match h with
      | And.intro hl hr =>
        rw [mem_id] at hr
        rw [hr] at hl
        exact hl
  . intro h
    unfold comp
    exact Exists.intro x.2 (And.intro h rfl)

theorem comp_id_left {f: α →ᵍ α}:
  id ○ f = f := by
  funext x
  apply eq_iff_iff.mpr
  apply Iff.intro
  . intro h
    unfold comp at h
    match h with
    | Exists.intro z h =>
      match h with
      | And.intro hl hr =>
        rw [mem_id] at hl
        rw [hl.symm] at hr
        exact hr
  . intro h
    unfold comp
    exact Exists.intro x.1 (And.intro rfl h)

end SRel
