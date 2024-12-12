import Semantics.Imp.Bexp

namespace Com
namespace Natural

inductive big_step: Com × State -> State -> Prop
  | skip:
    big_step (skip, s) s

  | ass:
    big_step (ass v a, s) (s[v <- a s])

  | cat (s'': State) (hcatl: big_step (c, s) s'') (hcatr: big_step (c', s'') s'):
    big_step (c++c', s) s'

  | iffalse (hcond: b s = false) (hifright: big_step (c', s) s'):
    big_step (if b then _ else c' end, s) s'

  | iftrue (hcond: b s) (hifleft: big_step (c, s) s'):
    big_step (if b then c else _ end, s) s'

  | whilefalse (hcond: b s = false):
    big_step (while b loop c end, s) s

  | whiletrue
    (s'': State) (hcond: b s) (hwhilestep: big_step (c, s) s'')
    (hwhilerest: big_step (while b loop c end, s'') s'):
    big_step (while b loop c end, s) s'

infix:10 " ==> " => big_step

private example:  ([|x := 5|], s0) ==> s0["x" <- 5] := big_step.ass

private example:
   ([|
      x := 2;
      if x <= 1 then
        y := 3
      else
        z := 4
      end
    |], s0)
    ==> s0["x" <- 2]["z" <- 4] :=
    big_step.cat (s0["x" <- 2]) big_step.ass (big_step.iffalse rfl big_step.ass)

private example:
  ([| x := 2; x := 3|], s0) ==> s0["x" <- 3] :=
  let h1: s0["x" <- 3] = s0["x" <- 2]["x" <- 3] :=
    Map.forget.symm
  h1 ▸ big_step.cat _ big_step.ass big_step.ass

-- factorial of x = 2
private example:
  ([|
    x := 2;
    y := 1;
    while 2 <= x loop
      y := y * x;
      x := x - 1
    end
  |], s0)
  ==> s0["x" <- 2]["y" <- 1]["y" <- 2]["x" <- 1] := by
  apply big_step.cat (s0["x" <- 2]["y" <- 1])
  apply big_step.cat (s0["x" <- 2])
  apply big_step.ass
  apply big_step.ass
  apply big_step.whiletrue (s0["x" <- 2]["y" <- 1]["y" <- 2]["x" <- 1])
  apply rfl
  apply big_step.cat (s0["x" <- 2]["y" <- 1]["y" <- 2])
  apply big_step.ass
  apply big_step.ass
  apply big_step.whilefalse
  apply rfl

/-
## Rewriting rules
-/

theorem skip_eq:
  ((skip, s) ==> s') = (s = s') :=
  propext {
    mp := fun (big_step.skip) => rfl,
    mpr := (· ▸ big_step.skip)
  }

theorem cat_eq:
  ((c++c', s) ==> s') = ∃s'', ((c, s) ==> s'') ∧ ((c', s'') ==> s') :=
  propext {
    mp := fun (big_step.cat s'' hcatl hcatr) => Exists.intro s'' (And.intro hcatl hcatr),
    mpr := fun (Exists.intro s'' (And.intro hcatl hcatr)) => big_step.cat s'' hcatl hcatr
  }

theorem if_eq:
  ((if b then c else c' end, s) ==> s')
    = bif b s then (c, s) ==> s' else (c', s) ==> s' :=
  propext {
    mp := fun hmp => match hmp with
      | big_step.iftrue hb h | big_step.iffalse hb h => hb ▸ h,
    mpr := match hb: b s with
      | true => (big_step.iftrue hb .)
      | false => (big_step.iffalse hb .)
  }

theorem if_eq':
  ((if b then c else c' end, s) ==> s')
    = ((bif b s then c else c', s) ==> s') :=
  propext {
    mp := fun hmp => match hmp with
      | big_step.iftrue hcond hif | big_step.iffalse hcond hif =>
        hcond ▸ hif,
    mpr := match hcond: b s with
      | true => (big_step.iftrue hcond .)
      | false => (big_step.iffalse hcond .)
  }

theorem while_eq:
  ((while b loop c end, s) ==> s') =
    bif b s then
      ∃s'', ((c, s) ==> s'') ∧ ((while b loop c end, s'') ==> s')
    else
      s = s' :=
  propext {
    mp := fun hmp => match hmp with
      | big_step.whiletrue s'' hcond hwhilestep hwhilerest =>
        hcond ▸ (Exists.intro s'' (And.intro hwhilestep hwhilerest))
      | big_step.whilefalse hb => hb ▸ rfl,
    mpr := match hb: b s with
      | true => fun (Exists.intro s'' (And.intro hwhilestep hwhilerest)) =>
        big_step.whiletrue s'' hb hwhilestep hwhilerest
      | false => (. ▸ big_step.whilefalse hb)
  }

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c c' := ∀{s s': State}, ((c, s) ==> s') <-> ((c', s) ==> s')
  iseqv := {
    refl := fun _ => Iff.rfl
    symm := (Iff.symm .)
    trans := fun h1 h2 => h1.trans h2
  }

theorem skipl: (skip++c) ≈ c := {
    mp := fun (big_step.cat _ hcatl hcatr) => skip_eq.mp hcatl ▸ hcatr,
    mpr := (big_step.cat _ big_step.skip .)
  }

theorem skipr: (c++skip) ≈ c := {
    mp := fun (big_step.cat _ hc hd) => skip_eq.mp hd ▸ hc,
    mpr := (big_step.cat _ · big_step.skip)
  }

theorem cond_true (hb: b ≈ Bexp.true):
  if b then c else c' end ≈ c := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem cond_false (hb: b ≈ Bexp.false):
  if b then c else c' end ≈ c' := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem loop_unfold:
  while b loop c end ≈
    if b then c++while b loop c end else skip end := by
  intro s _s''
  rw [if_eq']
  constructor
  . intro hmp
    match hmp with
    | big_step.whiletrue s' hb hc hw => exact hb ▸ big_step.cat s' hc hw
    | big_step.whilefalse hb => exact hb ▸ big_step.skip
  . match hb: b s with
    | false =>
      intro (big_step.skip)
      exact big_step.whilefalse hb
    | true =>
      intro (big_step.cat s' hc hw)
      exact big_step.whiletrue s' hb hc hw

/-
## Non termination
-/

theorem loop_tt (htrue: b ≈ Bexp.true):
  Not ((while b loop c end, s) ==> s') := by
  intro hmp
  generalize hconf: (while b loop c end, s) = conf at hmp
  induction hmp generalizing s with
  | whiletrue _ _ _ _ _ ihw =>
    match hconf with
    | Eq.refl _ => exact ihw rfl
  | whilefalse hb =>
    match hconf with
    | Eq.refl _ =>
      rw [htrue] at hb
      contradiction
  | _ =>
    match Prod.mk.injEq _ _ _ _ ▸ hconf with
    | ⟨_, _⟩ => contradiction

/-
## Determinism
-/

theorem deterministic {conf: Com × State}
  (hps: conf ==> s) (hps': conf ==> s'): s = s' :=
  by induction hps generalizing s' with
  | skip => match hps' with | big_step.skip => rfl
  | ass => match hps' with | big_step.ass => rfl
  | cat _ _ _ ihc ihc₂ =>
    match hps' with
    | big_step.cat _ hc hc₂ =>
      exact ihc₂ (ihc hc ▸ hc₂)
  | iftrue hb _ ihc =>
    match hps' with
    | big_step.iftrue _ hc =>
      exact ihc hc
    | big_step.iffalse hb₁ _ =>
      rw [hb] at hb₁
      contradiction
  | iffalse hb _ ihc₂ =>
    match hps' with
    | big_step.iftrue hb₁ _ =>
      rw [hb] at hb₁
      contradiction
    | big_step.iffalse _ hd =>
      exact ihc₂ hd
  | whiletrue _ hb _ _ ihc ihw =>
    match hps' with
    | big_step.whiletrue _ _ hc hw =>
      exact ihw (ihc hc ▸ hw)
    | big_step.whilefalse hb₁ =>
      rw [hb] at hb₁
      contradiction
  | whilefalse hb =>
    match hps' with
    | big_step.whiletrue _ hb₁ _ _ =>
      rw [hb] at hb₁
      contradiction
    | big_step.whilefalse _ => rfl

end Natural
end Com
