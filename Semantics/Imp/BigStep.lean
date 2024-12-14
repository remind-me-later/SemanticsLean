import Semantics.Imp.Bexp

namespace Com

inductive BigStep: Com × State -> State -> Prop
  | skip:
    BigStep (skip, s) s

  | ass:
    BigStep (ass v a, s) (s[v <- a s])

  | cat (s'': State) (hcatl: BigStep (c, s) s'') (hcatr: BigStep (c', s'') s'):
    BigStep (c++c', s) s'

  | iffalse (hcond: b s = false) (hifright: BigStep (c', s) s'):
    BigStep (if b then _ else c' end, s) s'

  | iftrue (hcond: b s) (hifleft: BigStep (c, s) s'):
    BigStep (if b then c else _ end, s) s'

  | whilefalse (hcond: b s = false):
    BigStep (while b loop c end, s) s

  | whiletrue
    (s'': State) (hcond: b s) (hwhilestep: BigStep (c, s) s'')
    (hwhilerest: BigStep (while b loop c end, s'') s'):
    BigStep (while b loop c end, s) s'

infix:10 " ==> " => BigStep

namespace BigStep

private example: ([|x := 5|], s0) ==> s0["x" <- 5] := ass

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
    cat (s0["x" <- 2]) ass (iffalse rfl ass)

private example:
  ([| x := 2; x := 3|], s0) ==> s0["x" <- 3] :=
  let h1: s0["x" <- 3] = s0["x" <- 2]["x" <- 3] :=
    Map.forget.symm
  h1 ▸ cat _ ass ass

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
  apply cat (s0["x" <- 2]["y" <- 1])
  apply cat (s0["x" <- 2])
  apply ass
  apply ass
  apply whiletrue (s0["x" <- 2]["y" <- 1]["y" <- 2]["x" <- 1])
  apply rfl
  apply cat (s0["x" <- 2]["y" <- 1]["y" <- 2])
  apply ass
  apply ass
  apply whilefalse
  apply rfl

/-
## Rewriting rules
-/

theorem skip_eq:
  ((Com.skip, s) ==> s') = (s = s') :=
  propext {
    mp := fun (skip) => rfl,
    mpr := (· ▸ skip)
  }

theorem cat_eq:
  ((c++c', s) ==> s') = ∃s'', ((c, s) ==> s'') ∧ ((c', s'') ==> s') :=
  propext {
    mp := fun (cat s'' hcatl hcatr) => Exists.intro s'' (And.intro hcatl hcatr),
    mpr := fun (Exists.intro s'' (And.intro hcatl hcatr)) => cat s'' hcatl hcatr
  }

theorem if_eq:
  ((if b then c else c' end, s) ==> s')
    = bif b s then (c, s) ==> s' else (c', s) ==> s' :=
  propext {
    mp := fun hmp => match hmp with
      | iftrue hb h | iffalse hb h => hb ▸ h,
    mpr := match hb: b s with
      | true => (iftrue hb .)
      | false => (iffalse hb .)
  }

theorem if_eq':
  ((if b then c else c' end, s) ==> s')
    = ((bif b s then c else c', s) ==> s') :=
  propext {
    mp := fun hmp => match hmp with
      | iftrue hcond hif | iffalse hcond hif =>
        hcond ▸ hif,
    mpr := match hcond: b s with
      | true => (iftrue hcond .)
      | false => (iffalse hcond .)
  }

theorem while_eq:
  ((while b loop c end, s) ==> s') =
    bif b s then
      ∃s'', ((c, s) ==> s'') ∧ ((while b loop c end, s'') ==> s')
    else
      s = s' :=
  propext {
    mp := fun hmp => match hmp with
      | whiletrue s'' hcond hwhilestep hwhilerest =>
        hcond ▸ (Exists.intro s'' (And.intro hwhilestep hwhilerest))
      | whilefalse hb => hb ▸ rfl,
    mpr := match hb: b s with
      | true => fun (Exists.intro s'' (And.intro hwhilestep hwhilerest)) =>
        whiletrue s'' hb hwhilestep hwhilerest
      | false => (. ▸ whilefalse hb)
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

theorem skipl: (Com.skip++c) ≈ c := {
    mp := fun (cat _ hcatl hcatr) => skip_eq.mp hcatl ▸ hcatr,
    mpr := (cat _ skip .)
  }

theorem skipr: (c++Com.skip) ≈ c := {
    mp := fun (cat _ hc hd) => skip_eq.mp hd ▸ hc,
    mpr := (cat _ · skip)
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
    if b then c++while b loop c end else Com.skip end := by
  intro s _s''
  rw [if_eq']
  constructor
  . intro hmp
    match hmp with
    | whiletrue s' hb hc hw => exact hb ▸ cat s' hc hw
    | whilefalse hb => exact hb ▸ skip
  . match hb: b s with
    | false =>
      intro (skip)
      exact whilefalse hb
    | true =>
      intro (cat s' hc hw)
      exact whiletrue s' hb hc hw

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
  | skip => match hps' with | skip => rfl
  | ass => match hps' with | ass => rfl
  | cat _ _ _ ihc ihc₂ =>
    match hps' with
    | cat _ hc hc₂ =>
      exact ihc₂ (ihc hc ▸ hc₂)
  | iftrue hb _ ihc =>
    match hps' with
    | iftrue _ hc =>
      exact ihc hc
    | iffalse hb₁ _ =>
      rw [hb] at hb₁
      contradiction
  | iffalse hb _ ihc₂ =>
    match hps' with
    | iftrue hb₁ _ =>
      rw [hb] at hb₁
      contradiction
    | iffalse _ hd =>
      exact ihc₂ hd
  | whiletrue _ hb _ _ ihc ihw =>
    match hps' with
    | whiletrue _ _ hc hw =>
      exact ihw (ihc hc ▸ hw)
    | whilefalse hb₁ =>
      rw [hb] at hb₁
      contradiction
  | whilefalse hb =>
    match hps' with
    | whiletrue _ hb₁ _ _ =>
      rw [hb] at hb₁
      contradiction
    | whilefalse _ => rfl

end BigStep
end Com
