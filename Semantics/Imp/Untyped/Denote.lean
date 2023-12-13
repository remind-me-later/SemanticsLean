import Semantics.Imp.Untyped.Bexp

import Mathlib.Data.Set.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Data.Set.Lattice
import Mathlib.Order.FixedPoints

namespace SRel

/-
# Relational denotational semantics

From Concrete semantics with Isabelle
-/

notation:20 α " →ᵍ " β => Set (α × β)

def id: α →ᵍ α := {p | p.1 = p.2}

@[simp] theorem mem_id {a b: α}:
  (a, b) ∈ @id α ↔ a = b := Iff.rfl

def comp (f g: α →ᵍ α): α →ᵍ α :=
  {x | ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g}

infixl:90 " ○ " => SRel.comp

@[simp] theorem mem_comp {f g: α →ᵍ α}:
  x ∈ f ○ g ↔ ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g := Iff.rfl

theorem comp_mono {α: Type} {f g h k : Set (α × α)} (h₁ : f ⊆ h) (h₂ : g ⊆ k) : f ○ g ⊆ h ○ k :=
  λ _ ⟨z, h, h'⟩ ↦ ⟨z, h₁ h, h₂ h'⟩

end SRel

namespace Com

def denote_loop (b: Bexp) (f: State →ᵍ State): (State →ᵍ State) →o (State →ᵍ State) := {
  toFun := λ g ↦ Set.ite {s | b⇓s.1} (f ○ g) SRel.id
  monotone' := λ _ _ h ↦ Set.ite_mono _ (SRel.comp_mono le_rfl h) le_rfl
}

def denote: Com → (State →ᵍ State)
  | skip       => SRel.id
  | ass x a    => {s | s.2 = s.1⟪x ≔ a⇓s.1⟫}
  | c;;d       => c.denote ○ d.denote
  | cond b c d => Set.ite {s | b⇓s.1} c.denote d.denote
  | loop b c   => OrderHom.lfp $ denote_loop b c.denote

notation (priority := high) "⟦" c "⟧" => denote c

#simp (σ₀, σ₀⟪"x"≔5⟫⟪"x"≔1⟫) ∈ ⟦⦃x = 5; if x <= 1 {skip} else {x = 1}⦄⟧
#simp [denote] (σ₀, σ₀⟪"x"≔5⟫) ∈ ⟦⦃x = 5; while x <= 1 {x = 1}⦄⟧

namespace denote

@[simp]
instance equiv: Setoid Com := ⟨(⟦·⟧ = ⟦·⟧), ⟨(refl ⟦.⟧), symm, Eq.trans⟩⟩

theorem skipl: (skip;;c) ≈ c := by
  simp [HasEquiv.Equiv, denote, SRel.comp]

theorem skipr: (c;;skip) ≈ c := by
  simp [HasEquiv.Equiv, denote, SRel.comp]

theorem loop_unfold: loop b c ≈ cond b (c;;loop b c) skip := by
  simp [HasEquiv.Equiv]
  exact Eq.symm $ OrderHom.map_lfp $ denote_loop b ⟦c⟧

/-
## Congruence
-/

theorem cat_congr (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
  (c₁;;d₁) ≈ (c₂;;d₂) := by
  simp [HasEquiv.Equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem cond_congr (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
  (cond b c₁ d₁) ≈ (cond b c₂ d₂) := by
  simp [HasEquiv.Equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem loop_congr (hc: c₁ ≈ c₂):
  (loop b c₁) ≈ (loop b c₂) := by
  simp [HasEquiv.Equiv, denote]
  exact hc ▸ rfl

end denote
end Com
