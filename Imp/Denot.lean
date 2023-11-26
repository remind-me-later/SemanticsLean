import Imp.Bexp

import Mathlib.Data.Set.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

def SRel.id: Set (α × α) := {p | p.1 = p.2}

@[simp] theorem SRel.mem_id (a b: α):
  (a, b) ∈ @id α ↔ a = b := Iff.rfl

def SRel.comp (r₁ r₂: Set (α × α)): Set (α × α) :=
  {a | ∃z, (a.1, z) ∈ r₁ ∧ (z, a.2) ∈ r₂}

infixl:90 " ○ " => SRel.comp

@[simp] theorem SRel.mem_comp (r₁ r₂: Set (α × α)):
  a ∈ r₁ ○ r₂ ↔ (∃z, (a.1, z) ∈ r₁ ∧ (z, a.2) ∈ r₂) := Iff.rfl

def SRel.restrictDomain (r: Set (α × α)) (p: α → Prop): Set (α × α) :=
  {a ∈ r | p a.1}

infixl:90 " ⇃ " => SRel.restrictDomain

@[simp] theorem SRel.mem_restrictDomain (r: Set (α × α)) (p: α → Prop):
  a ∈ r ⇃ p ↔ a ∈ r ∧ p a.1 := Iff.rfl

theorem SRel.monotone_comp [PartialOrder α]
    (f g: α → Set (β × β)) (hf: Monotone f)
    (hg: Monotone g):
  Monotone (λ a ↦ f a ○ g a) :=
  sorry

theorem SRel.monotone_restrictDomain [PartialOrder α]
    (f : α → Set (β × β)) (p: β → Prop) (hf: Monotone f):
  Monotone (λ a ↦ f a ⇃ p) :=
  sorry

def Com.Γ (b: Bexp) (f: Set (State × State)): Set (State × State) →o Set (State × State) := {
  toFun := (λ g ↦ (f ○ g ⇃ λ s↦b↓s) ∪ (SRel.id ⇃ λ s↦b↓s=false))
  monotone' := by
    apply Monotone.union
    . apply SRel.monotone_restrictDomain
      apply SRel.monotone_comp
      . exact monotone_const
      . exact monotone_id
    . apply SRel.monotone_restrictDomain
      exact monotone_const
}

@[simp]
def Com.red: Com → Set (State × State)
  | skip      => SRel.id
  | x ≔ a     => {s | s.2 = s.1⟦x↦a↓s.1⟧}
  | c;;d      => red c ○ red d
  | ife b c d => (red c ⇃ λ s↦b↓s) ∪ (red d ⇃ λ s↦b↓s=false)
  | wle b c   => OrderHom.lfp (Γ b (red c))

notation (priority := high) "⟦" c "⟧" => Com.red c

#simp ⟦⦃x ≔ 5; if x=1 {skip} else {x ≔ 1}⦄⟧

instance Com.red.equiv: Setoid Com where
  r c d := ⟦c⟧ = ⟦d⟧
  iseqv := {
    refl := λ _ ↦ Eq.refl _
    symm := Eq.symm
    trans := (· ▸ ·)
  }

-- theorem Com.red.cat_congr (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
--   (c₁;;d) ≈ (c₂;;d₂) :=
--   by
--     unfold red
--     exact hc ▸ hd ▸ rfl
