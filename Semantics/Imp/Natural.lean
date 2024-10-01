import Semantics.Imp.Bexp

namespace Com
namespace Natural

inductive step: Com → State → State → Prop
  | skip:
    step skip s s

  | ass:
    step (x = a) s (s⟪x ≔ a⇓s⟫)

  | cat t
    (hc: step c s t) (hd: step d t u):
    step (c;;d) s u

  | cond_true {b: Bexp}
    (hb: b⇓s = true) (hc: step c s t):
    step if b then c else d end s t

  | cond_false {b: Bexp}
    (hb: b⇓s = false) (hd: step d s t):
    step if b then c else d end s t

  | loop_true {b: Bexp} u
    (hb: b⇓s = true) (hc: step c s u)
    (hw: step while b loop c end u t):
    step while b loop c end s t

  | loop_false {b: Bexp}
    (hb: b⇓s = false):
    step while b loop c end s s

notation:10 s " ⊢ " c " ⟹ " t => step c s t

private def x := "x"
private def z := "z"

private example: σ₀ ⊢ ⦃x = 5⦄ ⟹ σ₀⟪x ≔ 5⟫ := step.ass
private example:
  σ₀ ⊢ ⦃x = 2; if x <= 1 {y = 3} else {z = 4}⦄ ⟹ σ₀⟪x ≔ 2⟫⟪z ≔ 4⟫ :=
    step.cat _ step.ass $ step.cond_false rfl step.ass
private example:
  σ₀ ⊢ ⦃x = 2; x = 3⦄ ⟹ σ₀⟪x ≔ 3⟫ := by
  have h1: σ₀⟪x ≔ 3⟫ = σ₀⟪x ≔ 2⟫⟪x ≔ 3⟫ := TotalMap.clobber.symm
  rw [h1]
  apply step.cat _ step.ass step.ass

/-
## Rewriting rules
-/

theorem skip_iff: (s ⊢ skip ⟹ t) = (s = t) := by
  apply propext
  constructor <;> intro h
  . cases h; rfl
  . exact h ▸ step.skip

theorem cat_iff:
  (s ⊢ c;;d ⟹ t) = ∃ w, (s ⊢ c ⟹ w) ∧ (w ⊢ d ⟹ t) := by
  apply propext
  constructor <;> intro h
  . cases h with
    | cat t h1 h2 =>
      exact ⟨t, ⟨h1, h2⟩⟩
  . cases h with
    | intro w h =>
      exact step.cat w h.1 h.2

theorem cond_iff:
  (s ⊢ if b then c else d end ⟹ t)
    = bif b⇓s then (s ⊢ c ⟹ t) else (s ⊢ d ⟹ t) := by
  apply propext
  constructor <;> intro h
  . cases h with
    | cond_true hb hc => exact hb ▸ hc
    | cond_false hb hc => exact hb ▸ hc
  . cases hb: b⇓s with
    | true => exact step.cond_true hb $ (cond_true (s ⊢ c ⟹ t) _) ▸ hb ▸ h
    | false => exact step.cond_false hb $ (cond_false _ (s ⊢ d ⟹ t)) ▸ hb ▸ h

theorem cond_iff':
  (s ⊢ if b then c else d end ⟹ t)
    = (s ⊢ bif b⇓s then c else d ⟹ t) := by
  rw [cond_iff]
  cases b⇓s with
  | false => rw [cond_false, cond_false]
  | true => rw [cond_true, cond_true]

theorem loop_iff: (s ⊢ while b loop c end ⟹ t) =
  bif b⇓s then ∃w, (s ⊢ c ⟹ w) ∧ (w ⊢ while b loop c end ⟹ t) else s = t := by
  apply propext
  constructor <;> intro h
  . cases h with
    | loop_true t hb hc hw => exact hb ▸ ⟨t, ⟨hc, hw⟩⟩
    | loop_false hb => exact hb ▸ rfl
  . cases hb: b⇓s with
    | true =>
      rw [hb] at h
      cases h with
      | intro w h =>
        exact step.loop_true w hb h.1 h.2
    | false =>
      exact (hb ▸ h) ▸ step.loop_false hb

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

theorem skipl: (skip;;c) ≈ c := by
  intro _ _
  constructor
  . intro h
    cases h with
    | cat _ hc hd =>
      exact skip_iff.mp hc ▸ hd
  . exact (step.cat _ step.skip ·)

theorem skipr: (c;;skip) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat _ hc hd =>
      exact skip_iff.mp hd ▸ hc
  . exact (step.cat _ · step.skip)

theorem cond_true (h: b ≈ Bexp.tt): if b then c else d end ≈ c := by
  intro _ _
  rw [cond_iff, h]
  rfl

theorem cond_false (h: b ≈ Bexp.ff): if b then c else d end ≈ d := by
  intro _ _
  rw [cond_iff, h]
  rfl

theorem loop_unfold:
  while b loop c end ≈ if b then (c;;while b loop c end) else skip end := by
  intro s t
  constructor <;> intro h
  . rw [cond_iff]
    cases h with
    | loop_true w hb hc hw => exact hb ▸ step.cat w hc hw
    | loop_false hb => exact hb ▸ step.skip
  . rw [loop_iff]
    rw [cond_iff] at h
    cases hb: b⇓s <;> rw [hb] at h
    . exact skip_iff.mp h
    . exact cat_iff.mp h

/-
## Non termination
-/

theorem loop_tt (h: b ≈ Bexp.tt):
  ¬(s ⊢ while b loop c end ⟹ t) := by
  intro h1
  generalize h2: while b loop c end = ww at h1
  induction h1 with
  | loop_true _ _ _ _ _ ih2 => cases h2; apply ih2; rfl
  | loop_false hb => cases h2; rw [h] at hb; contradiction
  | _ => cases h2

/-
## Determinism
-/

theorem deterministic {c: Com}
  (h1: w ⊢ c ⟹ s) (h2: w ⊢ c ⟹ t): s = t :=
  by induction h1 generalizing t with
  | cat _ _ _ ihc ihd =>
    cases h2 with
    | cat _ hc hd =>
      exact ihd (ihc hc ▸ hd)
  | cond_true hb _ ih =>
    cases h2 with
    | cond_true _ hd =>
      exact ih hd
    | cond_false hb1 hd =>
      rw [hb] at hb1
      contradiction
  | cond_false hb _ ih =>
    cases h2 with
    | cond_true hb1 hd =>
      rw [hb] at hb1
      contradiction
    | cond_false _ hd =>
      exact ih hd
  | loop_true _ hb _ _ ihc ihw =>
    cases h2 with
    | loop_true _ _ hc hw =>
      exact ihw (ihc hc ▸ hw)
    | loop_false hb1 =>
      rw [hb] at hb1
      contradiction
  | loop_false hb =>
    cases h2 with
    | loop_true _ hb1 =>
      rw [hb] at hb1
      contradiction
    | loop_false => rfl
  | _ => cases h2; rfl

end Natural
end Com
