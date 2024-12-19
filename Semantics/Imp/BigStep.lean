import Semantics.Imp.Bexp

namespace Com

inductive BigStep: Com × State -> State -> Prop
  | skip: BigStep ({}, s) s
  | ass: BigStep (ass v a, s) (s[v <- a s])
  | cat (s'': State) (hcatl: BigStep (c, s) s'') (hcatr: BigStep (c', s'') s'):
    BigStep (c++c', s) s'
  | ifFalse (hcond: b s = false) (hifright: BigStep (c', s) s'):
    BigStep (ifElse b _ c', s) s'
  | ifTrue (hcond: b s) (hifleft: BigStep (c, s) s'):
    BigStep (ifElse b c _, s) s'
  | whileFalse (hcond: b s = false):
    BigStep (whileLoop b c, s) s
  | whileTrue (s'': State) (hcond: b s) (hwhilestep: BigStep (c, s) s'')
    (hwhilerest: BigStep (whileLoop b c, s'') s'):
    BigStep (whileLoop b c, s) s'

infix:10 " ==> " => BigStep

namespace BigStep

private example: ([|x = 5|], s0) ==> s0["x" <- 5] := ass

private example:
   ([|
      x = 2;
      if x <= 1 {
        y = 3
      } else {
        z = 4
      }
    |], s0)
    ==> s0["x" <- 2]["z" <- 4] :=
    cat (s0["x" <- 2]) ass (ifFalse rfl ass)

private example:
  ([| x = 2; x = 3|], s0) ==> s0["x" <- 3] :=
  let h1: s0["x" <- 3] = s0["x" <- 2]["x" <- 3] :=
    Map.forget.symm
  h1 ▸ cat _ ass ass

-- factorial of x = 2
private example:
  ([|
    x = 2; y = 1;
    while 2 <= x {
      y = y * x;
      x = x - 1
    }
  |], s0)
  ==> s0["x" <- 2]["y" <- 1]["y" <- 2]["x" <- 1] := by
  apply cat (s0["x" <- 2]["y" <- 1])
  apply cat (s0["x" <- 2])
  apply ass
  apply ass
  apply whileTrue (s0["x" <- 2]["y" <- 1]["y" <- 2]["x" <- 1])
  apply rfl
  apply cat (s0["x" <- 2]["y" <- 1]["y" <- 2])
  apply ass
  apply ass
  apply whileFalse
  apply rfl

/-
## Rewriting rules
-/

theorem skip_eq: (({}, s) ==> s') <-> (s = s') := {
    mp := fun (skip) => rfl,
    mpr := (· ▸ skip)
  }

theorem cat_eq:
  ((c++c', s) ==> s') <-> ∃s'', ((c, s) ==> s'') ∧ ((c', s'') ==> s') := {
    mp := fun (cat s'' hcatl hcatr) => ⟨s'', hcatl, hcatr⟩,
    mpr := fun ⟨s'', hcatl, hcatr⟩ => cat s'' hcatl hcatr
  }

theorem if_eq: ((ifElse b c c', s) ==> s')
    <-> cond (b s) ((c, s) ==> s') ((c', s) ==> s') := {
    mp := fun hmp => match hmp with
      | ifTrue hcond hstep | ifFalse hcond hstep =>
        hcond ▸ hstep,
    mpr := match hb: b s with
      | true => (ifTrue hb .)
      | false => (ifFalse hb .)
  }

theorem if_eq': ((ifElse b c c', s) ==> s')
    <-> ((cond (b s) c c', s) ==> s') := {
    mp := fun hmp => match hmp with
      | ifTrue hcond hif | ifFalse hcond hif =>
        hcond ▸ hif,
    mpr := match hcond: b s with
      | true => (ifTrue hcond .)
      | false => (ifFalse hcond .)
  }

theorem while_eq:
  ((whileLoop b c, s) ==> s') <->
    cond (b s)
      (∃s'', ((c, s) ==> s'') ∧ ((whileLoop b c, s'') ==> s'))
      (s = s') := {
    mp := fun hmp => match hmp with
      | whileTrue s'' hcond hwhilestep hwhilerest =>
        hcond ▸ ⟨s'', hwhilestep, hwhilerest⟩
      | whileFalse hb => hb ▸ rfl,
    mpr := match hb: b s with
      | true => fun ⟨s'', hwhilestep, hwhilerest⟩ =>
        whileTrue s'' hb hwhilestep hwhilerest
      | false => (. ▸ whileFalse hb)
  }

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c c' := ∀{s s': State}, ((c, s) ==> s') <-> ((c', s) ==> s')
  iseqv := {
    refl := fun _ => Iff.rfl
    symm := (Iff.symm .)
    trans := (Iff.trans . .)
  }

theorem skipl {c: Com}: ({}++c) ≈ c := {
  mp := fun (cat _ hcatl hcatr) => skip_eq.mp hcatl ▸ hcatr,
  mpr := (cat _ skip .)
}

theorem skipr {c: Com}: (c++{}) ≈ c := {
  mp := fun (cat _ hc hd) => skip_eq.mp hd ▸ hc,
  mpr := (cat _ · skip)
}

theorem cond_true (hb: b ≈ Bexp.true): ifElse b c c' ≈ c := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem cond_false (hb: b ≈ Bexp.false): ifElse b c c' ≈ c' := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem loop_unfold: whileLoop b c ≈ ifElse b (c++whileLoop b c) {} := by
  intro s _s''
  rw [if_eq']
  exact {
    mp := fun hmp => match hmp with
      | whileTrue s' hb hc hw => hb ▸ cat s' hc hw
      | whileFalse hb => hb ▸ skip,
    mpr := match hb: b s with
      | false => fun (skip) => whileFalse hb
      | true => fun (cat s' hc hw) => whileTrue s' hb hc hw
  }

/-
## Non termination
-/

theorem loop_tt (htrue: b ≈ Bexp.true): ¬((whileLoop b c, s) ==> s') := by
  intro hmp
  generalize hconf: (whileLoop b c, s) = conf at hmp
  induction hmp generalizing s with
  | whileTrue _ _ _ _ _ ihw =>
    match hconf with
    | Eq.refl _ => exact ihw rfl
  | whileFalse hb =>
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
| cat _ _ _ ihcatl ihcatr =>
  match hps' with
  | cat _ hcatl hcatr =>
    exact ihcatr (ihcatl hcatl ▸ hcatr)
| ifTrue hcond _ ihifleft =>
  match hps' with
  | ifTrue _ hifleft => exact ihifleft hifleft
  | ifFalse hcond' _ =>
    have hcontra := hcond ▸ hcond'
    contradiction
| ifFalse hcond _ ihifright =>
  match hps' with
  | ifTrue hcond' _ =>
    have hcontra := hcond ▸ hcond'
    contradiction
  | ifFalse _ hifright =>
    exact ihifright hifright
| whileTrue _ hcond _ _ ihwhilestep ihwhilerest =>
  match hps' with
  | whileTrue _ _ hwhilestep hwhilerest =>
    exact ihwhilerest (ihwhilestep hwhilestep ▸ hwhilerest)
  | whileFalse hcond' =>
    have hcontra := hcond ▸ hcond'
    contradiction
| whileFalse hcond =>
  match hps' with
  | whileTrue _ hcond' _ _ =>
    have hcontra := hcond ▸ hcond'
    contradiction
  | whileFalse _ => rfl

end BigStep
end Com
