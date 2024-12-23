import Semantics.Imp.Bexp
import Semantics.KnasterTarski

/-
# Relational denotational semantics

From Concrete semantics with Isabelle
-/

namespace Com

private def denote_while (b: Bexp) (f: Set (State × State)):
  Set (State × State) → Set (State × State) :=
  fun g => Set.ite {(s, _) | b s} (f ○ g) SRel.id

def denote: Com → Set (State × State)
  | skip => SRel.id
  | ass v a => {(s, t) | t = s[v ← a s]}
  | cat c c' => c.denote ○ c'.denote
  | ifElse b c c' => Set.ite {(s, _) | b s} c.denote c'.denote
  | whileLoop b c => Fix.lfp $ denote_while b c.denote

theorem denote_while_mono: monotone (denote_while b c) :=
  fun _ _ hmp =>
  Set.ite_mono _ (SRel.comp_mono PartialOrder.le_rfl hmp) PartialOrder.le_rfl

notation (priority := high) "[[" c "]]" => denote c

#check (s0, s0["x"←5]["x"←1]) ∈ [[[|x = 5; if x <= 1 {skip} else {x = 1}|]]]
#check (s0, s0["x"←5]) ∈ [[[|x = 5; while x <= 1 {x = 1}|]]]

namespace Denotational

instance equiv: Setoid Com where
  r a b := [[a]] = [[b]]
  iseqv := {
    refl := fun _ => rfl,
    symm := Eq.symm
    trans := Eq.trans
  }

theorem skipl:
  (skip++c) ≈ c := by
  simp only [HasEquiv.Equiv, equiv, denote, SRel.id_comp]

theorem skipr:
  (c++skip) ≈ c := by
  simp only [HasEquiv.Equiv, equiv, denote, SRel.comp_id]

theorem while_unfold:
  whileLoop b c ≈ ifElse b (c++whileLoop b c) skip :=
  Fix.lfp_eq _ denote_while_mono

/-
## Congruence
-/

theorem cat_congr {c c' d₁ d₂: Com} (hc: c ≈ c') (hd: d₁ ≈ d₂):
  (c++d₁) ≈ (c'++d₂) := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem cond_congr (hc: c1 ≈ c2) (hd: d1 ≈ d2):
  ifElse b c1 d1 ≈ ifElse b c2 d2 := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem loop_congr (hc: c1 ≈ c2): whileLoop b c1 ≈ whileLoop b c2 := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ rfl

end Denotational
end Com
