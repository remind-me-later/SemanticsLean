import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com

inductive SmallStep: Com × State -> Com × State -> Prop where
  | ass: SmallStep (ass v a, s) ({}, s[v <- a s])
  | skipCat: SmallStep ({}++c, s) (c, s)
  | cat (hstep: SmallStep (c, s) (c', s')):
    SmallStep (c++c'', s) (c'++c'', s')
  | ifElse: SmallStep (ifElse b c c', s) (cond (b s) c c', s)
  | whileLoop:
    SmallStep (whileLoop b c, s) (cond (b s) (c++whileLoop b c) {}, s)

infixl:10 " ~> " => SmallStep

namespace SmallStep

private example: ([|x = 1; while x <= 2 {x = x + 1}|], s0) ~>
  ([|skip; while x <= 2 {x = x + 1}|], s0["x" <- 1]) := cat ass

theorem cat_eq: ((c++c'', s) ~> conf)
  <-> ((∃c' s', ((c, s) ~> (c', s')) ∧ conf = (c'++c'', s'))
    ∨ (c = {} ∧ conf = (c'', s))) := {
    mp := fun hmp => match hmp with
      | skipCat => Or.inr ⟨rfl, rfl⟩
      | cat h => Or.inl ⟨_, _, h, rfl⟩,
    mpr := fun hmpr => match hmpr with
      | Or.inl ⟨_c', _s', hl, hr⟩ => hr ▸ cat hl
      | Or.inr ⟨hl, hr⟩ => hl ▸ hr ▸ skipCat
  }

theorem cond_eq: ((.ifElse b c c', s) ~> conf)
  <-> (b s ∧ conf = (c, s) ∨ b s = false ∧ conf = (c', s)) := {
    mp := fun hmp => match hb: b s with
      | false => match hmp with | ifElse => Or.inr ⟨rfl, hb ▸ rfl⟩
      | true => match hmp with | ifElse => Or.inl ⟨rfl, hb ▸ rfl⟩,
    mpr := fun hmpr =>
      have hss: conf = (cond (b s) c c', s) := match hb: b s with
        | true => match hb ▸ hmpr with | Or.inl ⟨_, hr⟩ => hr
        | false => match hb ▸ hmpr with | Or.inr ⟨_, hr⟩ => hr
      hss ▸ ifElse
  }

theorem cond_false (hb: b s = false): ((.ifElse b c c', s) ~> conf)
  <-> (conf = (c', s)) := by
  rw [cond_eq, hb]
  exact ⟨fun (Or.inr ⟨rfl, h⟩) => h, (Or.inr ⟨rfl, .⟩)⟩

infixl:10 " ~>* " => ReflTrans SmallStep

private example: ([|x = 1; while x <= 1 {x = x + 1}|], s0) ~>*
    ({}, s0["x" <- 1]["x" <- 2]) := by
  apply ReflTrans.head (cat ass) (ReflTrans.head skipCat _)
  apply ReflTrans.head whileLoop
  have hs : s0["x" <- Aexp.eval 1 s0] = s0["x" <- 1] := rfl
  have hcond : (Bexp.le (Aexp.var "x") 1) (s0["x" <- 1]) = true := rfl
  rw [hs, hcond]
  apply ReflTrans.head (cat ass)
  apply ReflTrans.head skipCat
  apply ReflTrans.head whileLoop
  have hs : s0["x" <- 1]["x" <- (Aexp.var "x" + 1) (s0["x" <- 1])] =
    s0["x" <- 1]["x" <- 2] := rfl
  have hcond : (Bexp.le (Aexp.var "x") 1) (s0["x" <- 1]["x" <- 2])
    = false := rfl
  rw [hs, hcond]
  apply ReflTrans.refl

theorem star.cat_skip_cat (hc: (c, s) ~>* ({}, s')):
  (c++c', s) ~>* ({}++c', s') :=
  .lift (fun (c, s) => (c++c', s)) (cat .) hc

theorem star.cat (hc: (c, s) ~>* ({}, s')) (hc': (c', s') ~>* ({}, s'')):
  (c++c', s) ~>* ({}, s'') :=
  .trans (cat_skip_cat hc) $ .trans (.single skipCat) hc'

theorem star.cat_no_influence (hc: (c, s) ~>* ({}, s)):
  (c++c', s) ~>* (c', s) :=
  .trans (cat_skip_cat hc) $ .single skipCat

end SmallStep
end Com
