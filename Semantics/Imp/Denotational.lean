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
  rw [denote.eq_5, denote.eq_1, OrderHom.lfp]
  rw [←Set.inf_eq]
  rw [W.OrderHom]
  unfold Com.W
  unfold Bexp.eval
  unfold Set.sInter
  unfold Set.ite
  unfold OrderHom.pfp
  simp only
  apply Set.ext
  intro x
  rw [Set.mem_comprehend]
  constructor
  . intro h
    apply h ∅
    rw [Set.mem_comprehend]
    intro _ hl
    rw [SRel.id_comp, Set.empty_inter] at hl
    match hl with
    | .inl h => exact h
    | .inr h => exact Set.diff_univ _ ▸ h
  . exact (absurd . (Set.mem_empty _))
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
  r := ([[.]] = [[.]])
  iseqv := {
    refl := fun _ => rfl,
    symm := Eq.symm
    trans := Eq.trans
  }

theorem equiv_eq (c c': Com): c ≈ c' ↔ [[c]] = [[c']] := Iff.rfl
theorem append_eq (c c': Com): [[c++c']] = [[c]] ○ [[c']] := rfl

theorem skipl: (skip++c) ≈ c := by
  rw [equiv_eq, append_eq, denote.eq_1]
  exact SRel.id_comp

theorem skipr: (c++skip) ≈ c := by
  rw [equiv_eq, append_eq, denote.eq_1]
  exact SRel.comp_id

theorem while_unfold:
  whileLoop b c ≈ ifElse b (c++whileLoop b c) skip :=
  (W.OrderHom b c.denote).lfp_eq

/-
## Congruence
-/

theorem cat_congr {c c' d d': Com} (hc: c ≈ c') (hd: d ≈ d'):
  (c++d) ≈ (c'++d') := by
  rw [equiv_eq, append_eq, append_eq]
  exact hc ▸ hd ▸ rfl

theorem cond_congr (hc: c ≈ c') (hd: d ≈ d'):
  ifElse b c d ≈ ifElse b c' d' := by
  rw [equiv_eq, denote.eq_4]
  exact hc ▸ hd ▸ rfl

theorem loop_congr (hc: c ≈ c'): whileLoop b c ≈ whileLoop b c' := by
  rw [equiv_eq, denote.eq_5]
  exact hc ▸ rfl

end Denotational
end Com
