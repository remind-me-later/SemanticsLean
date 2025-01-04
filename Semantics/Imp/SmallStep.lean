import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com

inductive SmallStep: Com × State → Com × State → Prop where
  | ass: SmallStep (ass v a, s) (∅, s[v ← a s])
  | skipCat: SmallStep (∅++c, s) (c, s)
  | cat (hstep: SmallStep (c, s) (c', s')):
    SmallStep (c++c'', s) (c'++c'', s')
  | ifElse: SmallStep (ifElse b c c', s) (cond (b s) c c', s)
  | whileLoop:
    SmallStep (whileLoop b c, s) (cond (b s) (c++whileLoop b c) ∅, s)

infixl:100 " ~> " => SmallStep

namespace SmallStep

private example: ([|x = 1; while x <= 2 {x = x + 1}|], s0) ~>
  ([|skip; while x <= 2 {x = x + 1}|], s0["x" ← 1]) := cat ass

theorem cat_eq: (c++c'', s) ~> x
  ↔ ((∃c' s', (c, s) ~> (c', s') ∧ x = (c'++c'', s'))
    ∨ (c = ∅ ∧ x = (c'', s))) := {
    mp := fun hmp => match hmp with
      | skipCat => .inr ⟨rfl, rfl⟩
      | cat h => .inl ⟨_, _, h, rfl⟩,
    mpr := fun hmpr => match hmpr with
      | .inl ⟨_c', _s', hl, hr⟩ => hr ▸ cat hl
      | .inr ⟨hl, hr⟩ => hl ▸ hr ▸ skipCat
  }

theorem cond_eq: (.ifElse b c c', s) ~> x
  ↔ (b s ∧ x = (c, s) ∨ b s = false ∧ x = (c', s)) := {
    mp := fun hmp => match hb: b s with
      | false => match hmp with | ifElse => .inr ⟨rfl, hb ▸ rfl⟩
      | true => match hmp with | ifElse => .inl ⟨rfl, hb ▸ rfl⟩,
    mpr := fun hmpr =>
      have hss: x = (cond (b s) c c', s) := match hb: b s with
        | true => match hb ▸ hmpr with | .inl ⟨_, hr⟩ => hr
        | false => match hb ▸ hmpr with | .inr ⟨_, hr⟩ => hr
      hss ▸ ifElse
  }

theorem cond_false (hb: b s = false): (.ifElse b c c', s) ~> x ↔ x = (c', s) :=
  by
  rw [cond_eq, hb]
  exact ⟨fun (.inr ⟨rfl, h⟩) => h, (.inr ⟨rfl, .⟩)⟩

infixl:100 " ~>* " => ReflTrans SmallStep

private example: ([|x = 1; while x <= 1 {x = x + 1}|], s0) ~>*
    (∅, s0["x" ← 1]["x" ← 2]) := by
  apply ReflTrans.head (cat ass) (ReflTrans.head skipCat _)
  apply ReflTrans.head whileLoop
  have hs : s0["x" ← Aexp.eval 1 s0] = s0["x" ← 1] := rfl
  have hcond : (Bexp.le (Aexp.var "x") 1) (s0["x" ← 1]) = true := rfl
  rw [hs, hcond]
  apply ReflTrans.head (cat ass)
  apply ReflTrans.head skipCat
  apply ReflTrans.head whileLoop
  have hs : s0["x" ← 1]["x" ← (Aexp.var "x" + 1) (s0["x" ← 1])] =
    s0["x" ← 1]["x" ← 2] := rfl
  have hcond : (Bexp.le (Aexp.var "x") 1) (s0["x" ← 1]["x" ← 2])
    = false := rfl
  rw [hs, hcond]
  apply ReflTrans.refl

theorem star.cat_skip_cat (hc: (c, s) ~>* (∅, s')):
  (c++c', s) ~>* (∅++c', s') :=
  .lift (fun (c, s) => (c++c', s)) (cat .) hc

theorem star.cat (hc: (c, s) ~>* (∅, s')) (hc': (c', s') ~>* (∅, s'')):
  (c++c', s) ~>* (∅, s'') :=
  .trans (cat_skip_cat hc) $ .trans (.single skipCat) hc'

theorem star.cat_no_influence (hc: (c, s) ~>* (∅, s)):
  (c++c', s) ~>* (c', s) :=
  .trans (cat_skip_cat hc) $ .single skipCat

end SmallStep
end Com
