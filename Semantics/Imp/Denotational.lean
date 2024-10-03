import Semantics.Imp.Bexp
import Semantics.KnasterTarski

/-
# Relational denotational semantics

From Concrete semantics with Isabelle
-/

namespace Com

def denote_loop (b: Bexp) (f: State →ˢ State): (State →ˢ State) → (State →ˢ State) :=
  fun g => Set.ite {s | b⇓s.1} (f ○ g) SFun.id

def denote: Com → (State →ˢ State)
  | skip₁                  => SFun.id
  | ass₁ x a               => {s | s.2 = s.1⟪x ≔ a⇓s.1⟫}
  | c;;d                   => c.denote ○ d.denote
  | if b then c else d end => Set.ite {s | b⇓s.1} c.denote d.denote
  | while b loop c end     => Fix.lfp $ denote_loop b c.denote

theorem monotone_denote_loop: monotone (denote_loop b c) :=
  fun _ _ h => Set.ite_mono _ (SFun.comp_mono PartialOrder.le_rfl h) PartialOrder.le_rfl

notation (priority := high) "⟦" c "⟧" => denote c

#check (σ₀, σ₀⟪"x"≔5⟫⟪"x"≔1⟫) ∈ ⟦⦃x = 5; if x <= 1 then skip else x = 1 end⦄⟧
#check (σ₀, σ₀⟪"x"≔5⟫) ∈ ⟦⦃x = 5; while x <= 1 loop x = 1 end⦄⟧

namespace denote

instance equiv: Setoid Com where
  r a b := ⟦a⟧ = ⟦b⟧
  iseqv := {
    refl := fun _ => rfl,
    symm := Eq.symm
    trans := Eq.trans
  }

theorem skipl: (skip₁;;c) ≈ c :=
  by simp only [HasEquiv.Equiv, equiv, denote, SFun.id_comp]

theorem skipr: (c;;skip₁) ≈ c :=
  by simp only [HasEquiv.Equiv, equiv, denote, SFun.comp_id]

theorem while_unfold:
  while b loop c end ≈ if b then c;; while b loop c end else skip₁ end :=
  Fix.lfp_eq _ monotone_denote_loop

/-
## Congruence
-/

theorem cat_congr (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
  (c₁;;d₁) ≈ (c₂;;d₂) := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem cond_congr (hc: c1 ≈ c2) (hd: d1 ≈ d2):
  if b then c1 else d1 end ≈ if b then c2 else d2 end := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem loop_congr (hc: c1 ≈ c2):
  while b loop c1 end ≈ while b loop c2 end := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ rfl

end denote
end Com
