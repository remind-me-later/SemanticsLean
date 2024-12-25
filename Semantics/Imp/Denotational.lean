import Semantics.Imp.Bexp
import Semantics.Lattice
import Semantics.Chain

/-
# Relational denotational semantics

From Concrete semantics with Isabelle
-/

namespace Com

private def W (b: Bexp) (f: Set (State × State)):
  Set (State × State) → Set (State × State) :=
  fun g => {(s, _) | b s}.ite (f ○ g) SRel.id

private theorem W.Monotone: Monotone (W b f) :=
  fun _ _ hmp =>
  Set.ite_mono _ (SRel.comp_mono Preorder.le_rfl hmp) Preorder.le_rfl

instance W.OrderHom (b: Bexp) (f: Set (State × State)):
  Set (State × State) →o Set (State × State) :=
    ⟨W b f, W.Monotone⟩


def denote: Com → Set (State × State)
  | skip => SRel.id
  | ass v a => {(s, t) | t = s[v ← a s]}
  | cat c c' => c.denote ○ c'.denote
  | ifElse b c c' => {(s, _) | b s}.ite c.denote c'.denote
  | whileLoop b c => (W.OrderHom b c.denote).lfp

notation (priority := high) "[[" c "]]" => denote c

#check (s0, s0["x"←5]["x"←1]) ∈ [[[|x = 5; if x <= 1 {skip} else {x = 1}|]]]
#check (s0, s0["x"←5]) ∈ [[[|x = 5; while x <= 1 {x = 1}|]]]

/-
## Computation
-/

private theorem W.Continuous: Continuous (W b f) := by {
    intro s hs
    apply Set.ext
    intro x
    constructor
    . simp [W, Set.iUnion]
      intro hx
      match hx with
      | Or.inl ⟨⟨w, _, i, hi⟩, hr⟩ =>
        exists i
        simp [Set.ite]
        apply Or.inl
        simp [SRel.comp]
        constructor
        . exists w
        . exact hr
      | Or.inr hr =>
        exists 0
        apply Or.inr hr
    . simp [W, Set.iUnion]
      intro ⟨i, hi⟩
      match hi with
      | Or.inl ⟨⟨w, hl, hrr⟩, hr⟩ =>
        apply Or.inl
        simp [SRel.comp]
        constructor
        . exists w
          apply And.intro hl
          exists i
        . exact hr
      | Or.inr hh =>
        apply Or.inr hh
  }

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
  (W.OrderHom b c.denote).lfp_eq

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
