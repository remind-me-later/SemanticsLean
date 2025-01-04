import Semantics.Imp.Bexp

namespace Com

inductive BigStep: Com × State → State → Prop
  | skip: BigStep (∅, s) s
  | ass: BigStep (ass v a, s) (s[v ← a s])
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

infix:100 " ==> " => BigStep

namespace BigStep

private example: ([|x = 5|], s0) ==> s0["x" ← 5] := ass

private example: ([|x = 2; if x <= 1 {y = 3} else {z = 4}|], s0)
  ==> s0["x" ← 2]["z" ← 4] :=
  cat (s0["x" ← 2]) ass (ifFalse rfl ass)

private example: ([| x = 2; x = 3|], s0) ==> s0["x" ← 3] :=
  have h1: s0["x" ← 3] = s0["x" ← 2]["x" ← 3] :=
    Map.forget.symm
  h1 ▸ cat _ ass ass

-- factorial of x = 2
private example: ([|x = 2; y = 1; while 2 <= x {y = y * x; x = x - 1}|], s0)
  ==> s0["x" ← 2]["y" ← 1]["y" ← 2]["x" ← 1] := by
  apply cat (s0["x" ← 2]["y" ← 1]) (cat (s0["x" ← 2]) ass ass)
  apply whileTrue (s0["x" ← 2]["y" ← 1]["y" ← 2]["x" ← 1])
  apply rfl
  apply cat (s0["x" ← 2]["y" ← 1]["y" ← 2]) ass ass
  apply whileFalse
  apply rfl

/-
## Rewriting rules
-/

theorem skip_eq: (∅, s) ==> s' ↔ s = s' := ⟨fun (skip) => rfl, (· ▸ skip)⟩

theorem cat_eq: (c++c', s) ==> s' ↔ ∃s'', (c, s) ==> s'' ∧ (c', s'') ==> s' := {
    mp := fun (cat s'' hcatl hcatr) => ⟨s'', hcatl, hcatr⟩,
    mpr := fun ⟨s'', hcatl, hcatr⟩ => cat s'' hcatl hcatr
  }

theorem if_eq: (ifElse b c c', s) ==> s'
    ↔ cond (b s) ((c, s) ==> s') ((c', s) ==> s') := {
    mp := fun hmp => match hmp with | ifTrue hc h | ifFalse hc h => hc ▸ h,
    mpr := match hb: b s with | true => (ifTrue hb .) | false => (ifFalse hb .)
  }

theorem if_eq': (ifElse b c c', s) ==> s' ↔ (cond (b s) c c', s) ==> s' := {
    mp := fun hmp => match hmp with | ifTrue hc h | ifFalse hc h => hc ▸ h,
    mpr := match hb: b s with | true => (ifTrue hb .) | false => (ifFalse hb .)
  }

theorem while_eq: (whileLoop b c, s) ==> s' ↔
  cond (b s) (∃s'', (c, s) ==> s'' ∧ (whileLoop b c, s'') ==> s') (s = s') := {
    mp := fun hmp => match hmp with
      | whileTrue s'' hc h hw => hc ▸ ⟨s'', h, hw⟩
      | whileFalse hb => hb ▸ rfl,
    mpr := match hb: b s with
      | true => fun ⟨s'', h, hw⟩ => whileTrue s'' hb h hw
      | false => (. ▸ whileFalse hb)
  }

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c c' := ∀{s s': State}, (c, s) ==> s' ↔ (c', s) ==> s'
  iseqv := ⟨fun _ => Iff.rfl, (Iff.symm .), (Iff.trans . .)⟩

theorem skipl {c: Com}: ∅++c ≈ c :=
  ⟨fun (cat _ hl hr) => skip_eq.mp hl ▸ hr, (cat _ skip .)⟩

theorem skipr {c: Com}: c++∅ ≈ c :=
  ⟨fun (cat _ hl hr) => skip_eq.mp hr ▸ hl, (cat _ · skip)⟩

theorem cond_true (hb: b ≈ Bexp.true): ifElse b c c' ≈ c := by
  intro _ _; rw [if_eq', hb]; rfl

theorem cond_false (hb: b ≈ Bexp.false): ifElse b c c' ≈ c' := by
  intro _ _; rw [if_eq', hb]; rfl

theorem loop_unfold: whileLoop b c ≈ ifElse b (c++whileLoop b c) ∅ := by
  intro s _; rw [if_eq', while_eq]
  match b s with
  | false => exact skip_eq.symm
  | true => exact ⟨fun ⟨_, hl, hr⟩ => cat _ hl hr,
    fun (cat s'' hl hr) => ⟨s'', hl, hr⟩⟩

/-
## Non termination
-/

theorem loop_tt: ¬(whileLoop .true c, s) ==> s' := by
  intro hmp
  generalize hx: (whileLoop .true c, s) = x at hmp
  induction hmp generalizing s with
  | whileTrue _ _ _ _ _ ihw => match hx with
    | Eq.refl _ => exact ihw rfl
  | whileFalse hb => match hx with
    | Eq.refl _ => contradiction
  | _ => match Prod.mk.injEq _ _ _ _ ▸ hx with
    | ⟨_, _⟩ => contradiction

def halts (c: Com) (s: State) := ∃s', (c, s) ==> s'

theorem exists_non_halting: ∃c, ∀s, ¬halts c s :=
  ⟨whileLoop .true ∅, fun s => not_exists.mpr (@loop_tt ∅ s .)⟩

/-
## Determinism
-/

theorem deterministic {x: Com × State}
  (hps: x ==> s) (hps': x ==> s'): s = s' :=
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
      have hcontra := Bool.false_eq_true ▸ (hcond ▸ hcond').symm
      exact False.elim hcontra
  | ifFalse hcond _ ihifright =>
    match hps' with
    | ifTrue hcond' _ =>
      have hcontra := Bool.false_eq_true ▸ hcond ▸ hcond'
      exact False.elim hcontra
    | ifFalse _ hifright =>
      exact ihifright hifright
  | whileTrue _ hcond _ _ ihwhilestep ihwhilerest =>
    match hps' with
    | whileTrue _ _ hwhilestep hwhilerest =>
      exact ihwhilerest (ihwhilestep hwhilestep ▸ hwhilerest)
    | whileFalse hcond' =>
      have hcontra := Bool.false_eq_true ▸ (hcond ▸ hcond').symm
      exact False.elim hcontra
  | whileFalse hcond =>
    match hps' with
    | whileTrue _ hcond' _ _ =>
      have hcontra := Bool.false_eq_true ▸ hcond ▸ hcond'
      exact False.elim hcontra
    | whileFalse _ => rfl

end BigStep
end Com
