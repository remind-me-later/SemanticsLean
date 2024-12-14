import Semantics.Imp.Bexp
import Semantics.KnasterTarski

/-
# Relational denotational semantics

From Concrete semantics with Isabelle
-/

namespace Com

private def denote_while (b: Bexp) (f: State ->s State):
  (State ->s State) -> (State ->s State) :=
  fun g => Set.ite {(s, _) | b s} (f ○ g) SFun.id

def denote: Com -> (State ->s State)
  | skip      => SFun.id
  | ass v a   => {(s, t) | t = s[v <- a s]}
  | cat c c' => denote c ○ denote c'
  | if b then c else c' end =>
      Set.ite {(s, _) | b s} (denote c) (denote c')
  | while b loop c end =>
      Fix.lfp (denote_while b (denote c))

theorem monotone_denote_loop: monotone (denote_while b c) :=
  fun _ _ hmp =>
  Set.ite_mono _ (SFun.comp_mono PartialOrder.le_rfl hmp) PartialOrder.le_rfl

notation (priority := high) "[[" c "]]" => denote c

#check (s0, s0["x"<-5]["x"<-1]) ∈ [[[|x := 5; if x <= 1 then skip else x := 1 end|]]]
#check (s0, s0["x"<-5]) ∈ [[[|x := 5; while x <= 1 loop x := 1 end|]]]

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
  simp only [HasEquiv.Equiv, equiv, denote, SFun.id_comp]

theorem skipr:
  (c++skip) ≈ c := by
  simp only [HasEquiv.Equiv, equiv, denote, SFun.comp_id]

theorem while_unfold:
  while b loop c end ≈ if b then c++ while b loop c end else skip end :=
  Fix.lfp_eq _ monotone_denote_loop

/-
## Congruence
-/

theorem cat_congr {c c' d₁ d₂: Com}
  (hc: c ≈ c') (hd: d₁ ≈ d₂):
  (c++d₁) ≈ (c'++d₂) := by
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

end Denotational
end Com
