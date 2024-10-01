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
  σ₀ ⊢ ⦃x = 2; x = 3⦄ ⟹ σ₀⟪x ≔ 3⟫ := by
  have h1: σ₀⟪x ≔ 3⟫ = σ₀⟪x ≔ 2⟫⟪x ≔ 3⟫ := TotalMap.clobber.symm
  rw [h1]
  exact step.catₙ _ step.assₙ step.assₙ

/-
## Rewriting rules
-/

theorem skip_iff: (s ⊢ skip₁ ⟹ t) ↔ (s = t) :=
  ⟨fun h => match h with | step.skipₙ => rfl,
    fun h => h ▸ step.skipₙ⟩

theorem cat_iff:
  (s ⊢ c;;d ⟹ t) ↔ ∃ w, (s ⊢ c ⟹ w) ∧ (w ⊢ d ⟹ t) :=
  ⟨fun h => match h with | step.catₙ t h1 h2 => ⟨t, ⟨h1, h2⟩⟩,
    fun h => match h with | Exists.intro w h => step.catₙ w h.1 h.2⟩

theorem if_iff:
  (s ⊢ if b then c else d end ⟹ t)
    ↔ bif b⇓s then (s ⊢ c ⟹ t) else (s ⊢ d ⟹ t) :=
  ⟨fun h => match h with
    | step.if₁ₙ hb hc | step.if₀ₙ hb hc => hb ▸ hc,
    fun h => match hb: b⇓s with
    | true => step.if₁ₙ hb $ cond_true (s ⊢ c ⟹ t) _ ▸ hb ▸ h
    | false => step.if₀ₙ hb $ cond_false _ (s ⊢ d ⟹ t) ▸ hb ▸ h⟩

theorem if_iff':
  (s ⊢ if b then c else d end ⟹ t)
    ↔ (s ⊢ bif b⇓s then c else d ⟹ t) :=
  ⟨fun h => match h with
    | step.if₁ₙ hb hc => hb ▸ hc
    | step.if₀ₙ hb hd => hb ▸ hd,
    fun h => match hb: b⇓s with
      | true => step.if₁ₙ hb $ cond_true c _ ▸ hb ▸ h
      | false => step.if₀ₙ hb $ cond_false _ d ▸ hb ▸ h⟩

theorem while_iff: (s ⊢ while b loop c end ⟹ t) ↔
  bif b⇓s then ∃w, (s ⊢ c ⟹ w) ∧ (w ⊢ while b loop c end ⟹ t) else s = t :=
  ⟨fun h => match h with
    | step.while₁ₙ t hb hc hw => hb ▸ ⟨t, ⟨hc, hw⟩⟩
    | step.while₀ₙ hb => hb ▸ rfl,
    fun h => match hb: b⇓s with
      | true =>
        match hb ▸ h with
        | Exists.intro w h => step.while₁ₙ w hb h.1 h.2
      | false => (hb ▸ h) ▸ step.while₀ₙ hb⟩

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c d := ∀ s t, (s ⊢ c ⟹ t) ↔ (s ⊢ d ⟹ t)
  iseqv := {
    refl := fun _ _ _ => Iff.rfl
    symm := (Iff.symm $ · · ·)
    trans := fun h1 h2 x n => Iff.trans (h1 x n) (h2 x n)
  }

theorem skipl: (skip₁;;c) ≈ c := fun _ _ =>
  ⟨fun h => match h with | step.catₙ _ hc hd => skip_iff.mp hc ▸ hd,
    fun h => step.catₙ _ step.skipₙ h⟩

theorem skipr: (c;;skip₁) ≈ c := fun _ _ =>
  ⟨fun h => match h with | step.catₙ _ hc hd => skip_iff.mp hd ▸ hc,
    fun h => step.catₙ _ h step.skipₙ⟩

theorem cond_true (h: b ≈ Bexp.true₁): if b then c else d end ≈ c := by
  intro _ _
  rw [if_iff, h]
  rfl

theorem cond_false (h: b ≈ Bexp.false₁): if b then c else d end ≈ d := by
  intro _ _
  rw [if_iff, h]
  rfl

theorem loop_unfold:
  while b loop c end ≈ if b then (c;;while b loop c end) else skip₁ end := by
  intro s t
  constructor <;> intro h
  . rw [if_iff]
    match h with
    | step.while₁ₙ w hb hc hw => exact hb ▸ step.catₙ w hc hw
    | step.while₀ₙ hb => exact hb ▸ step.skipₙ
  . rw [while_iff]
    rw [if_iff] at h
    match hb: b⇓s with
    | false =>
      let hh := hb ▸ h
      exact skip_iff.mp hh
    | true =>
      let hh := hb ▸ h
      exact cat_iff.mp hh

/-
## Non termination
-/

theorem loop_tt (h: b ≈ Bexp.true₁):
  ¬(s ⊢ while b loop c end ⟹ t) := fun h1 => by
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
