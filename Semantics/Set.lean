-- Our only dependency on mathlib
import Mathlib.Data.Set.Defs

/-
  # Set theorems
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
  ### Set theoretic (partial) functions

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
