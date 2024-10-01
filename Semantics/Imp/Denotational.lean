import Semantics.Imp.Bexp
import Semantics.KnasterTarski

/-
# Relational denotational semantics

From Concrete semantics with Isabelle
-/

namespace Com

def denote_loop (b: Bexp) (f: State →ᵍ State): (State →ᵍ State) → (State →ᵍ State) :=
  fun g => Set.ite {s | b⇓s.1} (f ○ g) SRel.id

def denote: Com → (State →ᵍ State)
  | skip                => SRel.id
  | ass x a             => {s | s.2 = s.1⟪x ≔ a⇓s.1⟫}
  | c;;d                => c.denote ○ d.denote
  | if b then c else d end => Set.ite {s | b⇓s.1} c.denote d.denote
  | while b loop c end   => lfp $ denote_loop b c.denote

@[simp]
theorem monotone_denote_loop: monotone (denote_loop b c) :=
  fun _ _ h => Set.ite_mono _ (SRel.comp_mono PartialOrder.le_rfl h) PartialOrder.le_rfl

notation (priority := high) "⟦" c "⟧" => denote c

-- #simp (σ₀, σ₀⟪"x"≔5⟫⟪"x"≔1⟫) ∈ ⟦⦃x = 5; if x <= 1 {skip} else {x = 1}⦄⟧
-- #simp (σ₀, σ₀⟪"x"≔5⟫) ∈ ⟦⦃x = 5; while x <= 1 {x = 1}⦄⟧

namespace denote

@[simp]
instance equiv: Setoid Com := ⟨(⟦·⟧ = ⟦·⟧), ⟨(Eq.refl ⟦.⟧), Eq.symm, Eq.trans⟩⟩

theorem skipl: (skip;;c) ≈ c :=
  by simp [HasEquiv.Equiv, denote]

theorem skipr: (c;;skip) ≈ c :=
  by simp [HasEquiv.Equiv, denote]

theorem loop_unfold:
  while b loop c end ≈ if b then c;; while b loop c end else skip end :=
  lfp_eq _ monotone_denote_loop

-- /-
-- ## Congruence
-- -/

theorem cat_congr (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
  (c₁;;d₁) ≈ (c₂;;d₂) := by
  simp [HasEquiv.Equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem cond_congr (hc: c1 ≈ c2) (hd: d1 ≈ d2):
  if b then c1 else d1 end ≈ if b then c2 else d2 end := by
  simp [HasEquiv.Equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem loop_congr (hc: c1 ≈ c2):
  while b loop c1 end ≈ while b loop c2 end := by
  simp [HasEquiv.Equiv, denote]
  exact hc ▸ rfl

end denote
end Com
