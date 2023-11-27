import Imp.Bexp

import Mathlib.Data.Set.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

-- Set relation denotational semantics,
-- aka graph of partial function
@[reducible]
def SRel α β := Set (α × β)

infixl:20 " →ˢ " => SRel

def SRel.id: α →ˢ α := {p | p.1 = p.2}

@[simp] theorem SRel.mem_id {a b: α}:
  (a, b) ∈ @id α ↔ a = b := Iff.rfl

def SRel.comp (f g: α →ˢ α): α →ˢ α :=
  {x | ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g}

infixl:90 " ○ " => SRel.comp

@[simp] theorem SRel.mem_comp {f g: α →ˢ α}:
  x ∈ f ○ g ↔ ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g := Iff.rfl

@[reducible]
def SRel.restrict (f: α →ˢ β) (s: Set α): α →ˢ β :=
  {x ∈ f | x.1 ∈ s}

theorem SRel.monotone_comp [PartialOrder α] {f g: α → (β →ˢ β)}
  (hf: Monotone f) (hg: Monotone g):
  Monotone λ x ↦ f x ○ g x :=
  λ _ _ h _ ⟨z, h₁, h₂⟩ => ⟨z, hf h h₁, hg h h₂⟩

theorem SRel.monotone_restrict [PartialOrder α] {f : α → (β →ˢ β)} {s: Set β}
  (hf: Monotone f):
  Monotone λ x ↦ restrict (f x) s :=
  λ _ _ h _ ⟨z, h₁⟩ ↦ ⟨hf h z, h₁⟩

def Com.Γ (b: Bexp) (f: State →ˢ State): (State →ˢ State) →o (State →ˢ State) := {
  toFun := λ g ↦ ((f ○ g).restrict {s | b↓s = true})
                    ∪ (SRel.id.restrict {s | b↓s = false})
  monotone' :=
    Monotone.union
    (SRel.monotone_restrict (SRel.monotone_comp monotone_const monotone_id))
    (SRel.monotone_restrict monotone_const)
}

def Com.denot: Com → (State →ˢ State)
  | skip       => SRel.id
  | ass x a    => {s | s.2 = s.1⟦x↦a↓s.1⟧}
  | c;;d       => c.denot ○ d.denot
  | cond b c d => (c.denot.restrict {s | b↓s = true})
                    ∪ (d.denot.restrict {s | b↓s = false})
  | wle b c    => OrderHom.lfp (Γ b c.denot)

notation (priority := high) "⟦" c "⟧" => Com.denot c

#simp (⟦⟧, ⟦"x"↦5⟧⟦"x"↦1⟧) ∈ ⟦⦃x = 5; if x == 1 {skip} else {x = 1}⦄⟧
#simp (⟦⟧, ⟦"x"↦5⟧) ∈ ⟦⦃x = 5; while x == 1 {x = 1}⦄⟧

@[simp]
instance Com.denot.equiv: Setoid Com where
  r := (⟦·⟧ = ⟦·⟧)
  iseqv := {
    refl := λ _ ↦ Eq.refl _
    symm := Eq.symm
    trans := (· ▸ ·)
  }

theorem Com.denot.cat_congr (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
  (c₁;;d₁) ≈ (c₂;;d₂) :=
  by
    simp [HasEquiv.Equiv, denot]
    exact hc ▸ hd ▸ rfl

theorem Com.denot.cond_congr (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
  (cond b c₁ d₁) ≈ (cond b c₂ d₂) :=
  by
    simp [HasEquiv.Equiv, denot]
    exact hc ▸ hd ▸ rfl

theorem Com.denot.wle_congr (hc: c₁ ≈ c₂):
  (wle b c₁) ≈ (wle b c₂) :=
  by
    simp [HasEquiv.Equiv, denot]
    exact hc ▸ rfl

theorem Com.denot.cat_skipl:
  (skip;;c) ≈ c :=
  by simp [HasEquiv.Equiv, denot, SRel.comp]

theorem Com.denot.cat_skipr:
  (c;;skip) ≈ c :=
  by simp [HasEquiv.Equiv, denot, SRel.comp]

theorem Com.denot.wle_unfold:
  wle b c ≈ cond b (c;;wle b c) skip := by
  simp [HasEquiv.Equiv]
  exact Eq.symm (OrderHom.map_lfp (Γ b ⟦c⟧))
