import Semantics.Imp.Untyped.Bexp

namespace Com
namespace Natural

inductive Step: Com → State → State → Prop
  | skip:
    Step skip s s

  | ass:
    Step (ass x a) s (s⟪x ≔ a⇓s⟫)

  | cat t
    (hc: Step c s t) (hd: Step d t u):
    Step (c;;d) s u

  | cond₁ {b: Bexp}
    (hb: b⇓s = true) (hc: Step c s t):
    Step (cond b c d) s t

  | cond₂ {b: Bexp}
    (hb: b⇓s = false) (hd: Step d s t):
    Step (cond b c d) s t

  | loop₁ {b: Bexp} u
    (hb: b⇓s = true) (hc: Step c s u) (hw: Step (loop b c) u t):
    Step (loop b c) s t

  | loop₂ {b: Bexp}
    (hb: b⇓s = false):
    Step (loop b c) s s

notation s " ⊢ " c " ⟹ " t => Step c s t

theorem demo₁: ⟪⟫ ⊢ ⦃x = 5⦄ ⟹ ⟪"x" ≔ 5⟫ := Step.ass

theorem demo₂:
  ⟪⟫ ⊢ ⦃x = 2; if x <= 1 {y = 3} else {z = 4}⦄ ⟹ ⟪"x" ≔ 2⟫⟪"z" ≔ 4⟫ :=
    Step.cat _ Step.ass $ Step.cond₂ rfl Step.ass

/-
## Rewriting rules
-/

theorem skip_iff: (s ⊢ skip ⟹ t) ↔ s = t := by
  apply Iff.intro <;> intro h
  . cases h; rfl
  . exact h ▸ Step.skip

theorem cat_iff: (s ⊢ c;;d ⟹ t) ↔ ∃ w, (s ⊢ c ⟹ w) ∧ (w ⊢ d ⟹ t) := by
  apply Iff.intro <;> intro h
  . cases h with | cat t h₁ h₂ =>
      exact ⟨t, ⟨h₁, h₂⟩⟩
  . cases h with | intro w h =>
      exact Step.cat w h.1 h.2

theorem cond_iff: (s ⊢ cond b c d ⟹ t) ↔ bif b⇓s then (s ⊢ c ⟹ t) else (s ⊢ d ⟹ t) := by
  constructor <;> intro h
  . cases h with
    | cond₁ hb hc => exact hb ▸ hc
    | cond₂ hb hc => exact hb ▸ hc
  . cases hb: b⇓s with
    | true => exact Step.cond₁ hb $ (cond_true (s ⊢ c ⟹ t) _) ▸ hb ▸ h
    | false => exact Step.cond₂ hb $ (cond_false _ (s ⊢ d ⟹ t)) ▸ hb ▸ h

theorem cond_iff': (s ⊢ cond b c d ⟹ t) ↔ (s ⊢ bif b⇓s then c else d ⟹ t) := by
  rw [cond_iff]; cases b⇓s <;> simp

theorem loop_iff: (s ⊢ loop b c ⟹ t) ↔
  (bif b⇓s then ∃ w, (s ⊢ c ⟹ w) ∧ (w ⊢ loop b c ⟹ t) else s = t) := by
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
        exact Step.loop₁ w hb h.1 h.2
    | false =>
      exact (hb ▸ h) ▸ Step.loop₂ hb

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
  . exact (Step.cat _ Step.skip ·)

theorem skipr: (c;;skip) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat _ hc hd =>
      exact skip_iff.mp hd ▸ hc
  . exact (Step.cat _ · Step.skip)

theorem cond_true (h: b ≈ Bexp.tt): cond b c d ≈ c := by
  intro _ _
  rw [cond_iff, h]
  rfl

theorem cond_false (h: b ≈ Bexp.ff): cond b c d ≈ d := by
  intro _ _
  rw [cond_iff, h]
  exact Iff.rfl

theorem loop_unfold:
  loop b c ≈ cond b (c;;loop b c) skip := by
  intro s t
  constructor <;> intro h
  . rw [cond_iff]
    cases h with
    | loop₁ w hb hc hw => exact hb ▸ Step.cat w hc hw
    | loop₂ hb => exact hb ▸ Step.skip
  . rw [loop_iff]
    rw [cond_iff] at h
    cases hb: b⇓s <;> rw [hb] at h
    . exact skip_iff.mp h
    . exact cat_iff.mp h

/-
## No termination
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

theorem determinist {c: Com} (h₁: w ⊢ c ⟹ s) (h₂: w ⊢ c ⟹ t): s = t :=
  by induction h₁ generalizing t with
  | cat _ _ _ ih₁ ih₂ => cases h₂ with
    | cat _ hc hd => exact ih₂ (ih₁ hc ▸ hd)

  | cond₁ hb _ ih => cases h₂ with
    | cond₁ _ hd => exact ih hd
    | cond₂ hb₁ hd => simp [hb] at hb₁

  | cond₂ hb _ ih => cases h₂ with
    | cond₁ hb₁ hd => simp [hb] at hb₁
    | cond₂ _ hd   => exact ih hd

  | loop₁ _ hb _ _ ih₁ ih₂ => cases h₂ with
    | loop₁ _ _ hc hw => exact ih₂ (ih₁ hc ▸ hw)
    | loop₂ hb₁ => simp [hb] at hb₁

  | loop₂ hb => cases h₂ with
    | loop₁ _ hb₁ => simp [hb] at hb₁
    | loop₂ => rfl

  | _ => cases h₂; rfl

end Natural
end Com
