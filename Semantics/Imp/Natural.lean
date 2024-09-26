import Semantics.Imp.Bexp

namespace Com
namespace Natural

inductive step: Com → State → State → Prop
  | skip:
    step skip s s

  | ass:
    step (ass x a) s (s⟪x ≔ a⇓s⟫)

  | cat t
    (hc: step c s t) (hd: step d t u):
    step (cat c d) s u

  | cond₁ {b: Bexp}
    (hb: b⇓s = true) (hc: step c s t):
    step (cond b c d) s t

  | cond₂ {b: Bexp}
    (hb: b⇓s = false) (hd: step d s t):
    step (cond b c d) s t

  | loop₁ {b: Bexp} u
    (hb: b⇓s = true) (hc: step c s u) (hw: step (loop b c) u t):
    step (loop b c) s t

  | loop₂ {b: Bexp}
    (hb: b⇓s = false):
    step (loop b c) s s

notation:10 s " ⊢ " c " ⟹ " t => step c s t

private def x := "x"
private def z := "z"

private example: σ₀ ⊢ ⦃x = 5⦄ ⟹ σ₀⟪x ≔ 5⟫ := step.ass
private example:
  σ₀ ⊢ ⦃x = 2; if x <= 1 {y = 3} else {z = 4}⦄ ⟹ σ₀⟪x ≔ 2⟫⟪z ≔ 4⟫ :=
    step.cat _ step.ass $ step.cond₂ rfl step.ass
private example:
  σ₀ ⊢ ⦃x = 2; x = 3⦄ ⟹ σ₀⟪x ≔ 3⟫ := by
  have h₁: σ₀⟪x ≔ 3⟫ = σ₀⟪x ≔ 2⟫⟪x ≔ 3⟫ := update_override.symm
  rw [h₁]
  apply step.cat _ step.ass step.ass

/-
## Rewriting rules
-/

theorem skip_iff: (s ⊢ skip ⟹ t) ↔ s = t := by
  apply Iff.intro <;> intro h
  . cases h; rfl
  . exact h ▸ step.skip

theorem cat_iff: (s ⊢ c;;d ⟹ t) ↔ ∃ w, (s ⊢ c ⟹ w) ∧ (w ⊢ d ⟹ t) := by
  apply Iff.intro <;> intro h
  . cases h with | cat t h₁ h₂ =>
      exact ⟨t, ⟨h₁, h₂⟩⟩
  . cases h with | intro w h =>
      exact step.cat w h.1 h.2

theorem cond_iff: (s ⊢ cond b c d ⟹ t) ↔ bif b⇓s then (s ⊢ c ⟹ t) else (s ⊢ d ⟹ t) := by
  constructor <;> intro h
  . cases h with
    | cond₁ hb hc => exact hb ▸ hc
    | cond₂ hb hc => exact hb ▸ hc
  . cases hb: b⇓s with
    | true => exact step.cond₁ hb $ (cond_true (s ⊢ c ⟹ t) _) ▸ hb ▸ h
    | false => exact step.cond₂ hb $ (cond_false _ (s ⊢ d ⟹ t)) ▸ hb ▸ h

theorem cond_iff': (s ⊢ cond b c d ⟹ t) ↔ (s ⊢ bif b⇓s then c else d ⟹ t) := by
  rw [cond_iff]
  cases b⇓s with
  | false => rw [cond_false, cond_false]
  | true => rw [cond_true, cond_true]

theorem loop_iff: (s ⊢ loop b c ⟹ t) ↔
  bif b⇓s then ∃ w, (s ⊢ c ⟹ w) ∧ (w ⊢ loop b c ⟹ t) else s = t := by
  apply Iff.intro <;> intro h
  . cases h with
    | loop₁ t hb hc hw =>
      exact hb ▸ ⟨t, ⟨hc, hw⟩⟩
    | loop₂ hb =>
      exact hb ▸ rfl
  . cases hb: b⇓s with
    | true =>
      rw [hb] at h
      cases h with | intro w h =>
        exact step.loop₁ w hb h.1 h.2
    | false =>
      exact (hb ▸ h) ▸ step.loop₂ hb

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c d := ∀ s t, (s ⊢ c ⟹ t) ↔ (s ⊢ d ⟹ t)
  iseqv := {
    refl := λ _ _ _ ↦ Iff.refl _
    symm := (Iff.symm $ · · ·)
    trans := λ h₁ h₂ x n ↦ Iff.trans (h₁ x n) (h₂ x n)
  }

theorem skipl: (skip;;c) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat _ hc hd =>
      exact skip_iff.mp hc ▸ hd
  . exact (step.cat _ step.skip ·)

theorem skipr: (c;;skip) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat _ hc hd =>
      exact skip_iff.mp hd ▸ hc
  . exact (step.cat _ · step.skip)

theorem cond_true (h: b ≈ Bexp.tt): cond b c d ≈ c := by
  intro _ _
  rw [cond_iff, h]
  exact Iff.rfl

theorem cond_false (h: b ≈ Bexp.ff): cond b c d ≈ d := by
  intro _ _
  rw [cond_iff, h]
  exact Iff.rfl

theorem loop_unfold:
  loop b c ≈ cond b (c;;loop b c) skip := by
  intro s t
  apply Iff.intro <;> intro h
  . rw [cond_iff]
    cases h with
    | loop₁ w hb hc hw => exact hb ▸ step.cat w hc hw
    | loop₂ hb => exact hb ▸ step.skip
  . rw [loop_iff]
    rw [cond_iff] at h
    cases hb: b⇓s <;> rw [hb] at h
    . exact skip_iff.mp h
    . exact cat_iff.mp h

/-
## Non termination
-/

theorem loop_tt (h: b ≈ Bexp.tt):
  ¬(s ⊢ loop b c ⟹ t) := by
  intro h₁
  generalize h₂: loop b c = ww at h₁
  induction h₁ with
  | loop₁ _ _ _ _ _ ih₂ => cases h₂; apply ih₂; rfl
  | loop₂ hb => cases h₂; rw [h] at hb; contradiction
  | _ => cases h₂

/-
## Determinism
-/

theorem deterministic {c: Com} (h₁: w ⊢ c ⟹ s) (h₂: w ⊢ c ⟹ t): s = t :=
  by induction h₁ generalizing t with
  | cat _ _ _ ih₁ ih₂ => cases h₂ with
    | cat _ hc hd => exact ih₂ (ih₁ hc ▸ hd)
  | cond₁ hb _ ih => cases h₂ with
    | cond₁ _ hd => exact ih hd
    | cond₂ hb₁ hd => rw [hb] at hb₁; contradiction
  | cond₂ hb _ ih => cases h₂ with
    | cond₁ hb₁ hd => rw [hb] at hb₁; contradiction
    | cond₂ _ hd   => exact ih hd
  | loop₁ _ hb _ _ ih₁ ih₂ => cases h₂ with
    | loop₁ _ _ hc hw => exact ih₂ (ih₁ hc ▸ hw)
    | loop₂ hb₁ => rw [hb] at hb₁; contradiction
  | loop₂ hb => cases h₂ with
    | loop₁ _ hb₁ => rw [hb] at hb₁; contradiction
    | loop₂ => rfl
  | _ => cases h₂; rfl

end Natural
end Com
