import Semantics.Set

/-
# Set theoretic relations
-/

namespace SRel

def id: Set (α × α) := {p | p.1 = p.2}

theorem mem_id: (a, b) ∈ id ↔ a = b :=
  Iff.rfl

def comp (f g: Set (α × α)): Set (α × α) :=
  {(x, z) | ∃y, (x, y) ∈ f ∧ (y, z) ∈ g}

infixl:90 " ○ " => SRel.comp

theorem mem_comp: x ∈ f ○ g ↔ ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g :=
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
