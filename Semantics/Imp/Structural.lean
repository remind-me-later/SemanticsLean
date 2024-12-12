import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com
namespace Structural

inductive small_step: Com × State -> Com × State -> Prop where
  | ass:
    small_step (ass v a, s) (skip, s[v <- a s])

  | skipcat:
    small_step (skip++c, s) (c, s)

  | cat (hstep: small_step (c, s) (c', s')):
    small_step (c++c'', s) (c'++c'', s')

  | ifelse:
    small_step (if b then c else c' end, s) (bif b s then c else c', s)

  | whileloop:
    small_step (while b loop c end, s)
          (bif b s then c++while b loop c end else skip, s)

infixl:10 " ~> " => small_step

private example:
  ([|x := 0; while x <= 2 loop x := x + 1 end|], s0) ~>
      ([|skip; while x <= 2 loop x := x + 1 end|], s0["x" <- 0]) :=
  small_step.cat small_step.ass

theorem cat_eq:
  ((c++c'', s) ~> conf)
    = ((∃c' s', ((c, s) ~> (c', s')) ∧ conf = (c'++c'', s'))
      ∨ (c = skip ∧ conf = (c'', s))) :=
  propext {
    mp := fun hmp => match hmp with
      | small_step.skipcat => Or.inr (And.intro rfl rfl)
      | small_step.cat h =>
        Or.inl (Exists.intro _ (Exists.intro _ (And.intro h rfl))),
    mpr := fun hmpr => match hmpr with
      | Or.inl (Exists.intro _c' (Exists.intro _s' (And.intro hl hr))) =>
        hr ▸ small_step.cat hl
      | Or.inr (And.intro hl hr) => hl ▸ hr ▸ small_step.skipcat
  }

theorem cond_eq:
  ((if b then c else c' end, s) ~> conf)
    = (b s ∧ conf = (c, s) ∨ b s = false ∧ conf = (c', s)) :=
  propext {
    mp := fun hmp => match hb: b s with
      | false => match hmp with | small_step.ifelse => Or.inr (And.intro rfl (hb ▸ rfl))
      | true => match hmp with | small_step.ifelse => Or.inl (And.intro rfl (hb ▸ rfl)),
    mpr := fun hmpr =>
      let hss: conf = (bif b s then c else c', s) :=
        match hb: b s with
        | true => match hb ▸ hmpr with | Or.inl (And.intro _ hr) => hr
        | false => match hb ▸ hmpr with | Or.inr (And.intro _ hr) => hr
      hss ▸ small_step.ifelse
  }

theorem cond_false (hb: b s = false):
  ((if b then c else c' end, s) ~> conf) = (conf = (c', s)) :=
  propext {
    mp := fun hmp => match hb ▸ cond_eq ▸ hmp with
      | Or.inr (And.intro _ hr) => hr,
    mpr := fun mp => cond_eq ▸ Or.inr (And.intro hb mp)
  }

infixl:10 " ~>* " => RTL small_step

theorem star.demo':
  ([|x := 2; while 0 <= x loop x := x + 1 end|], s0) ~>*
      ([|while 0 <= x loop x := x + 1 end|], s0["x" <- 2]) :=
  RTL.head (small_step.cat small_step.ass) (RTL.head small_step.skipcat RTL.refl)

theorem star.cat_skip_cat
  (hc: (c, s) ~>* (skip, s')):
  (c++c', s) ~>* (skip++c', s') :=
  RTL.lift (fun (c, s) => (c++c', s)) (fun h => small_step.cat h) hc

theorem star.cat
  (hc: (c, s) ~>* (skip, s'))
  (hc': (c', s') ~>* (skip, s'')):
  (c++c', s) ~>* (skip, s'') :=
  RTL.trans (cat_skip_cat hc) (RTL.trans (RTL.single small_step.skipcat) hc')

theorem star.cat_no_influence
  (hc: (c, s) ~>* (skip, s)):
  (c++c', s) ~>* (c', s) :=
  RTL.trans (cat_skip_cat hc) (RTL.single small_step.skipcat)

end Structural
end Com
