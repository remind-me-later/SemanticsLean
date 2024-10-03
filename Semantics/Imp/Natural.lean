import Semantics.Imp.Bexp

namespace Com
namespace Natural

inductive step: Com → State → State → Prop
  | skipₙ:
    step skip₁ s s

  | assₙ:
    step (x = a) s (s⟪x ≔ a⇓s⟫)

  | catₙ (t: State) (hc: step c s t) (hd: step d t u):
    step (c;;d) s u

  | if₀ₙ {b: Bexp} (hb: b⇓s = false) (hd: step d s t):
    step if b then c else d end s t

  | if₁ₙ {b: Bexp} (hb: b⇓s = true) (hc: step c s t):
    step if b then c else d end s t

  | while₀ₙ {b: Bexp} (hb: b⇓s = false):
    step while b loop c end s s

  | while₁ₙ {b: Bexp} (u: State) (hb: b⇓s = true) (hc: step c s u)
    (hw: step while b loop c end u t):
    step while b loop c end s t

notation:10 s " ⊢ " c " ⟹ " t => step c s t

private def x := "x"
private def z := "z"

private example: σ₀ ⊢ ⦃x = 5⦄ ⟹ σ₀⟪x ≔ 5⟫ := step.assₙ
private example:
  σ₀ ⊢ ⦃x = 2; if x <= 1 then y = 3 else z = 4 end⦄ ⟹ σ₀⟪x ≔ 2⟫⟪z ≔ 4⟫ :=
    step.catₙ _ step.assₙ $ step.if₀ₙ rfl step.assₙ
private example:
  σ₀ ⊢ ⦃x = 2; x = 3⦄ ⟹ σ₀⟪x ≔ 3⟫ :=
  let h1: σ₀⟪x ≔ 3⟫ = σ₀⟪x ≔ 2⟫⟪x ≔ 3⟫ := TotalMap.clobber.symm
  h1 ▸ step.catₙ _ step.assₙ step.assₙ

/-
## Rewriting rules
-/

theorem skip_eq: (s ⊢ skip₁ ⟹ t) = (s = t) :=
  propext {
    mp := λ (step.skipₙ) => rfl,
    mpr := (· ▸ step.skipₙ)
  }

theorem cat_eq:
  (s ⊢ c;;d ⟹ t) = ∃ w, (s ⊢ c ⟹ w) ∧ (w ⊢ d ⟹ t) :=
  propext {
    mp := λ (step.catₙ t h1 h2) => ⟨t, h1, h2⟩,
    mpr := λ ⟨w, h1, h2⟩ => step.catₙ w h1 h2
  }

theorem if_eq:
  (s ⊢ if b then c else d end ⟹ t)
    = bif b⇓s then (s ⊢ c ⟹ t) else (s ⊢ d ⟹ t) :=
  propext {
    mp := λ h => match h with
      | step.if₁ₙ hb h | step.if₀ₙ hb h => hb ▸ h,
    mpr := match hb: b⇓s with
      | true => λ h => step.if₁ₙ hb h
      | false => λ h => step.if₀ₙ hb h
  }

theorem if_eq':
  (s ⊢ if b then c else d end ⟹ t)
    = (s ⊢ bif b⇓s then c else d ⟹ t) :=
  propext $ {
    mp := λ h => match h with
      | step.if₁ₙ hb h | step.if₀ₙ hb h => hb ▸ h,
    mpr := match hb: b⇓s with
      | true => λ h => step.if₁ₙ hb h
      | false => λ h => step.if₀ₙ hb h
  }

theorem while_eq: (s ⊢ while b loop c end ⟹ t) =
  bif b⇓s then ∃w, (s ⊢ c ⟹ w) ∧ (w ⊢ while b loop c end ⟹ t) else s = t :=
  propext {
    mp := λ h => match h with
      | step.while₁ₙ t hb hc hw => hb ▸ ⟨t, hc, hw⟩
      | step.while₀ₙ hb => hb ▸ rfl,
    mpr := match hb: b⇓s with
      | true => λ ⟨w, h1, h2⟩ => step.while₁ₙ w hb h1 h2
      | false => λ h => h ▸ step.while₀ₙ hb
  }

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c d := ∀s t, (s ⊢ c ⟹ t) ↔ (s ⊢ d ⟹ t)
  iseqv := {
    refl := λ _ _ _ => Iff.rfl
    symm := (Iff.symm $ · · ·)
    trans := λ h1 h2 x n => Iff.trans (h1 x n) (h2 x n)
  }

theorem skipl: (skip₁;;c) ≈ c := λ _ _ =>
  {
    mp := λ (step.catₙ _ hc hd) => skip_eq.mp hc ▸ hd,
    mpr := λ h => step.catₙ _ step.skipₙ h
  }

theorem skipr: (c;;skip₁) ≈ c := λ _ _ =>
  {
    mp := λ (step.catₙ _ hc hd) => skip_eq.mp hd ▸ hc,
    mpr := λ h => step.catₙ _ h step.skipₙ
  }

theorem cond_true (h: b ≈ Bexp.true₁):
  if b then c else d end ≈ c := by
  intro _ _
  rw [if_eq, h]
  rfl

theorem cond_false (h: b ≈ Bexp.false₁):
  if b then c else d end ≈ d := by
  intro _ _
  rw [if_eq, h]
  rfl

theorem loop_unfold:
  while b loop c end ≈
    if b then (c;;while b loop c end) else skip₁ end := by
  intro s t
  rw [if_eq']
  constructor
  . intro h
    match h with
    | step.while₁ₙ w hb hc hw => exact hb ▸ step.catₙ w hc hw
    | step.while₀ₙ hb => exact hb ▸ step.skipₙ
  . match hb: b⇓s with
    | false =>
      intro (step.skipₙ)
      exact step.while₀ₙ hb
    | true =>
      intro (step.catₙ w hc hw)
      exact step.while₁ₙ w hb hc hw

/-
## Non termination
-/

theorem loop_tt (h: b ≈ Bexp.true₁):
  ¬(s ⊢ while b loop c end ⟹ t) := λ h1 => by
  generalize h2: while b loop c end = ww at h1
  induction h1 with
  | while₁ₙ _ _ _ _ _ ih2 =>
    match h2 with
    | Eq.refl _ => exact ih2 rfl
  | while₀ₙ hb =>
    match h2 with
    | Eq.refl _ =>
      rw [h] at hb
      contradiction
  | _ => contradiction

/-
## Determinism
-/

theorem deterministic {c: Com}
  (h1: w ⊢ c ⟹ s) (h2: w ⊢ c ⟹ t): s = t :=
  by induction h1 generalizing t with
  | skipₙ => match h2 with | step.skipₙ => rfl
  | assₙ => match h2 with | step.assₙ => rfl
  | catₙ _ _ _ ihc ihd =>
    match h2 with
    | step.catₙ _ hc hd =>
      exact ihd (ihc hc ▸ hd)
  | if₁ₙ hb _ ih =>
    match h2 with
    | step.if₁ₙ _ hd =>
      exact ih hd
    | step.if₀ₙ hb1 hd =>
      rw [hb] at hb1
      contradiction
  | if₀ₙ hb _ ih =>
    match h2 with
    | step.if₁ₙ hb1 _ =>
      rw [hb] at hb1
      contradiction
    | step.if₀ₙ _ hd =>
      exact ih hd
  | while₁ₙ _ hb _ _ ihc ihw =>
    match h2 with
    | step.while₁ₙ _ _ hc hw =>
      exact ihw (ihc hc ▸ hw)
    | step.while₀ₙ hb1 =>
      rw [hb] at hb1
      contradiction
  | while₀ₙ hb =>
    match h2 with
    | step.while₁ₙ _ hb1 _ _ =>
      rw [hb] at hb1
      contradiction
    | step.while₀ₙ _ => rfl

end Natural
end Com
