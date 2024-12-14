import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com

inductive SmallStep: Com × State -> Com × State -> Prop where
  | ass:
    SmallStep (ass v a, s) (skip, s[v <- a s])

  | skipcat:
    SmallStep (skip++c, s) (c, s)

  | cat (hstep: SmallStep (c, s) (c', s')):
    SmallStep (c++c'', s) (c'++c'', s')

  | ifelse:
    SmallStep (if b then c else c' end, s) (bif b s then c else c', s)

  | whileloop:
    SmallStep (while b loop c end, s)
          (bif b s then c++while b loop c end else skip, s)

infixl:10 " ~> " => SmallStep

namespace SmallStep

private example:
  ([|x := 0; while x <= 2 loop x := x + 1 end|], s0) ~>
      ([|skip; while x <= 2 loop x := x + 1 end|], s0["x" <- 0]) :=
  cat ass

theorem cat_eq:
  ((c++c'', s) ~> conf)
    = ((∃c' s', ((c, s) ~> (c', s')) ∧ conf = (c'++c'', s'))
      ∨ (c = skip ∧ conf = (c'', s))) :=
  propext {
    mp := fun hmp => match hmp with
      | skipcat => Or.inr (And.intro rfl rfl)
      | cat h =>
        Or.inl (Exists.intro _ (Exists.intro _ (And.intro h rfl))),
    mpr := fun hmpr => match hmpr with
      | Or.inl (Exists.intro _c' (Exists.intro _s' (And.intro hl hr))) =>
        hr ▸ cat hl
      | Or.inr (And.intro hl hr) => hl ▸ hr ▸ skipcat
  }

theorem cond_eq:
  ((if b then c else c' end, s) ~> conf)
    = (b s ∧ conf = (c, s) ∨ b s = false ∧ conf = (c', s)) :=
  propext {
    mp := fun hmp => match hb: b s with
      | false => match hmp with | ifelse => Or.inr (And.intro rfl (hb ▸ rfl))
      | true => match hmp with | ifelse => Or.inl (And.intro rfl (hb ▸ rfl)),
    mpr := fun hmpr =>
      let hss: conf = (bif b s then c else c', s) :=
        match hb: b s with
        | true => match hb ▸ hmpr with | Or.inl (And.intro _ hr) => hr
        | false => match hb ▸ hmpr with | Or.inr (And.intro _ hr) => hr
      hss ▸ ifelse
  }

theorem cond_false (hb: b s = false):
  ((if b then c else c' end, s) ~> conf) = (conf = (c', s)) :=
  propext {
    mp := fun hmp => match hb ▸ cond_eq ▸ hmp with
      | Or.inr (And.intro _ hr) => hr,
    mpr := fun mp => cond_eq ▸ Or.inr (And.intro hb mp)
  }

infixl:10 " ~>* " => RTL SmallStep

theorem star.demo':
  ([|x := 2; while 0 <= x loop x := x + 1 end|], s0) ~>*
      ([|while 0 <= x loop x := x + 1 end|], s0["x" <- 2]) :=
  RTL.head (cat ass) (RTL.head skipcat RTL.refl)

theorem star.cat_skip_cat
  (hc: (c, s) ~>* (skip, s')):
  (c++c', s) ~>* (skip++c', s') :=
  RTL.lift (fun (c, s) => (c++c', s)) (fun h => cat h) hc

theorem star.cat
  (hc: (c, s) ~>* (skip, s'))
  (hc': (c', s') ~>* (skip, s'')):
  (c++c', s) ~>* (skip, s'') :=
  RTL.trans (cat_skip_cat hc) (RTL.trans (RTL.single skipcat) hc')

theorem star.cat_no_influence
  (hc: (c, s) ~>* (skip, s)):
  (c++c', s) ~>* (c', s) :=
  RTL.trans (cat_skip_cat hc) (RTL.single skipcat)

end SmallStep
end Com
