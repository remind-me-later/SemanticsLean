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

private example: [[[|while true {skip}|]]] = ∅ := by {
  simp [denote, W.OrderHom]
  unfold Com.W
  unfold Bexp.eval
  simp [Set.ite, SRel.id_comp, ←Set.univ_def, Set.inter_univ, Set.diff_univ,
    Set.union_empty]
  simp [OrderHom.lfp, OrderHom.pfp, CompleteLattice.Inf, Preorder.le_refl,
    ←Set.univ_def]
  simp [Set.sInter_univ]
}

/-
## Computation
-/

private theorem W.ωContinuous: ωContinuous (W b f) := fun _ _ =>
  Set.ext fun _ => {
    mp := fun hx => match hx with
      | .inl ⟨⟨w, hwl, i, hwr⟩, hr⟩ => ⟨i, .inl ⟨⟨w, hwl, hwr⟩, hr⟩⟩
      | .inr hr => ⟨0, .inr hr⟩
    mpr := fun ⟨i, hi⟩ => match hi with
      | .inl ⟨⟨_w, hwl, hwr⟩, hr⟩ => .inl ⟨⟨_, hwl, i, hwr⟩, hr⟩
      | .inr hh => .inr hh
  }

instance W.ContinuousHom (b: Bexp) (f: Set (State × State)):
  (State × State) →ω (State × State) := {
    toFun := W b f
    monotone' := W.Monotone
    continuous' := W.ωContinuous
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
