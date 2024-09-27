import Mathlib.Data.Set.Defs

theorem subset_refl {α : Type} (x : Set α) : x ⊆ x := fun _ => id

theorem subset_trans {α : Type} {x y z : Set α} (h1 : x ⊆ y) (h2 : y ⊆ z) : x ⊆ z :=
  fun _ h => h2 (h1 h)

theorem subset_antisymm {α : Type} {x y : Set α} (h1 : x ⊆ y) (h2 : y ⊆ x) : x = y :=
  funext fun _ => propext ⟨fun h => h1 h, fun h => h2 h⟩

protected def Set.ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t

@[simp]
theorem Set.ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') :
    t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  fun _ h2 =>
    match h2 with
    | Or.inl h3 => Or.inl ⟨h h3.1, h3.2⟩
    | Or.inr h3 => Or.inr ⟨h' h3.1, h3.2⟩
