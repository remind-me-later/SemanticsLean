import Semantics.Imp.Bexp

namespace Com
namespace Natural

inductive step: Config → State → Prop
  | skipₙ:
    step (skip₁, s) s

  | assₙ:
    step (ass₁ v a, s) (s[v ← a s])

  | catₙ (s₂: State) (hc₁: step (c₁, s₁) s₂) (hc₂: step (c₂, s₂) s₃):
    step (c₁++c₂, s₁) s₃

  | if₀ₙ (hb: b s₁ = false) (hc₂: step (c₂, s₁) s₂):
    step (if b then c₁ else c₂ end, s₁) s₂

  | if₁ₙ (hb: b s₁ = true) (hc₁: step (c₁, s₁) s₂):
    step (if b then c₁ else c₂ end, s₁) s₂

  | while₀ₙ (hb: b s₁ = false):
    step (while b loop c end, s₁) s₁

  | while₁ₙ
    (s₂: State) (hb: b s₁ = true) (hc: step (c, s₁) s₂)
    (hw: step (while b loop c end, s₂) s₃):
    step (while b loop c end, s₁) s₃

infix:10 " ⟹ " => step

private example:  ([|x := 5|], s₀) ⟹ s₀["x" ← 5] := step.assₙ

private example:
   ([|
      x := 2;
      if x ≤ 1 then
        y := 3
      else
        z := 4
      end
    |], s₀)
    ⟹ s₀["x" ← 2]["z" ← 4] :=
    step.catₙ _ step.assₙ $ step.if₀ₙ rfl step.assₙ

private example:
  ([| x := 2; x := 3|], s₀) ⟹ s₀["x" ← 3] :=
  let h1: s₀["x" ← 3] = s₀["x" ← 2]["x" ← 3] :=
    Map.eval_last.symm
  h1 ▸ step.catₙ _ step.assₙ step.assₙ

/-
## Rewriting rules
-/

theorem skip_eq:
  ((skip₁, s₁) ⟹ s₂) = (s₁ = s₂) :=
  propext {
    mp := λ (step.skipₙ) ↦ rfl,
    mpr := (· ▸ step.skipₙ)
  }

theorem cat_eq:
  ((c₁++c₂, s₁) ⟹ s₃) = ∃s₂, ((c₁, s₁) ⟹ s₂) ∧ ((c₂, s₂) ⟹ s₃) :=
  propext {
    mp := λ (step.catₙ s₂ h₁ h₂) ↦ ⟨s₂, h₁, h₂⟩,
    mpr := λ ⟨s₂, h₁, h₂⟩ ↦ step.catₙ s₂ h₁ h₂
  }

theorem if_eq:
  ((if b then c₁ else c₂ end, s₁) ⟹ s₂)
    = bif b s₁ then (c₁, s₁) ⟹ s₂ else (c₂, s₁) ⟹ s₂ :=
  propext {
    mp := λ hmp ↦ match hmp with
      | step.if₁ₙ hb h | step.if₀ₙ hb h => hb ▸ h,
    mpr := match hb: b s₁ with
      | true => λ hmp ↦ step.if₁ₙ hb hmp
      | false => λ hmp ↦ step.if₀ₙ hb hmp
  }

theorem if_eq':
  ((if b then c₁ else c₂ end, s₁) ⟹ s₂)
    = ((bif b s₁ then c₁ else c₂, s₁) ⟹ s₂) :=
  propext {
    mp := λ hmp ↦ match hmp with
      | step.if₁ₙ hb h | step.if₀ₙ hb h => hb ▸ h,
    mpr := match hb: b s₁ with
      | true => λ hmp ↦ step.if₁ₙ hb hmp
      | false => λ hmp ↦ step.if₀ₙ hb hmp
  }

theorem while_eq:
  ((while b loop c end, s₁) ⟹ s₃) =
    bif b s₁ then
      ∃s₂, ((c, s₁) ⟹ s₂) ∧ ((while b loop c end, s₂) ⟹ s₃)
    else
      s₁ = s₃ :=
  propext {
    mp := λ hmp ↦ match hmp with
      | step.while₁ₙ s₂ hb hc hw => hb ▸ ⟨s₂, hc, hw⟩
      | step.while₀ₙ hb => hb ▸ rfl,
    mpr := match hb: b s₁ with
      | true => λ ⟨s₂, h₁, h₂⟩ ↦ step.while₁ₙ s₂ hb h₁ h₂
      | false => λ hmp ↦ hmp ▸ step.while₀ₙ hb
  }

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c₁ c₂ := ∀{s₁ s₂: State}, ((c₁, s₁) ⟹ s₂) ↔ ((c₂, s₁) ⟹ s₂)
  iseqv := {
    refl := λ _ _ _ ↦ Iff.rfl
    symm := λ h ↦ Iff.symm h
    trans := λ h1 h2 ↦ Iff.trans h1 h2
  }

theorem skipl:
  (skip₁++c) ≈ c :=
  {
    mp := λ (step.catₙ _ hc hd) ↦ skip_eq.mp hc ▸ hd,
    mpr := λ h ↦ step.catₙ _ step.skipₙ h
  }

theorem skipr:
  (c++skip₁) ≈ c :=
  {
    mp := λ (step.catₙ _ hc hd) ↦ skip_eq.mp hd ▸ hc,
    mpr := λ h ↦ step.catₙ _ h step.skipₙ
  }

theorem cond_true (hb: b ≈ Bexp.true₁):
  if b then c₁ else c₂ end ≈ c₁ := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem cond_false (hb: b ≈ Bexp.false₁):
  if b then c₁ else c₂ end ≈ c₂ := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem loop_unfold:
  while b loop c end ≈
    if b then c++while b loop c end else skip₁ end := by
  intro s₁ s₃
  rw [if_eq']
  constructor
  . intro hmp
    match hmp with
    | step.while₁ₙ s₂ hb hc hw => exact hb ▸ step.catₙ s₂ hc hw
    | step.while₀ₙ hb => exact hb ▸ step.skipₙ
  . match hb: b s₁ with
    | false =>
      intro (step.skipₙ)
      exact step.while₀ₙ hb
    | true =>
      intro (step.catₙ s₂ hc hw)
      exact step.while₁ₙ s₂ hb hc hw

/-
## Non termination
-/

theorem loop_tt (htrue: b ≈ Bexp.true₁):
  ¬((while b loop c end, s) ⟹ t) := by
  intro hmp
  generalize hconf: (while b loop c end, s) = conf at hmp
  induction hmp generalizing s with
  | while₁ₙ _ _ _ _ _ ihw =>
    match hconf with
    | Eq.refl _ => exact ihw rfl
  | while₀ₙ hb =>
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

theorem deterministic
  (hps₁: conf ⟹ s₁) (hps₂: conf ⟹ s₂): s₁ = s₂ :=
  by induction hps₁ generalizing s₂ with
  | skipₙ => match hps₂ with | step.skipₙ => rfl
  | assₙ => match hps₂ with | step.assₙ => rfl
  | catₙ _ _ _ ihc₁ ihc₂ =>
    match hps₂ with
    | step.catₙ _ hc₁ hc₂ =>
      exact ihc₂ (ihc₁ hc₁ ▸ hc₂)
  | if₁ₙ hb _ ihc₁ =>
    match hps₂ with
    | step.if₁ₙ _ hc₁ =>
      exact ihc₁ hc₁
    | step.if₀ₙ hb₁ _ =>
      rw [hb] at hb₁
      contradiction
  | if₀ₙ hb _ ihc₂ =>
    match hps₂ with
    | step.if₁ₙ hb₁ _ =>
      rw [hb] at hb₁
      contradiction
    | step.if₀ₙ _ hd =>
      exact ihc₂ hd
  | while₁ₙ _ hb _ _ ihc ihw =>
    match hps₂ with
    | step.while₁ₙ _ _ hc hw =>
      exact ihw (ihc hc ▸ hw)
    | step.while₀ₙ hb₁ =>
      rw [hb] at hb₁
      contradiction
  | while₀ₙ hb =>
    match hps₂ with
    | step.while₁ₙ _ hb₁ _ _ =>
      rw [hb] at hb₁
      contradiction
    | step.while₀ₙ _ => rfl

end Natural
end Com
