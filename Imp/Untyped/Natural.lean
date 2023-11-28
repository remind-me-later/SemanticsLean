import Imp.Untyped.Bexp

namespace Com

inductive Natural: Config → State → Prop
  | skip₁:
    Natural (skip, s) s

  | ass₁:
    Natural (ass x a, s) (s⟪x ≔ a⇓s⟫)

  | cat₁ t
    (hc: Natural (c, s) t) (hd: Natural (d, t) u):
    Natural (c;;d, s) u

  | cond₁ {b: Bexp}
    (hb: b⇓s = true) (hc: Natural (c, s) t):
    Natural (cond b c d, s) t

  | cond₂ {b: Bexp}
    (hb: b⇓s = false) (hd: Natural (d, s) t):
    Natural (cond b c d, s) t

  | loop₁ {b: Bexp} u
    (hb: b⇓s = true) (hc: Natural (c, s) u) (hw: Natural (loop b c, u) t):
    Natural (loop b c, s) t

  | loop₂ {b: Bexp}
    (hb: b⇓s = false):
    Natural (loop b c, s) s

infix:110 " ⟹ " => Natural

namespace Natural

theorem demo₁: (⦃x = 5⦄, ⟪⟫) ⟹ ⟪⟫⟪"x"≔5⟫ := ass₁

theorem demo₂:
  (⦃x = 2; if x <= 1 {y = 3} else {z = 4}⦄, ⟪⟫) ⟹
  (⟪⟫⟪"x"≔2⟫⟪"z"≔4⟫) := cat₁ _ ass₁ $ cond₂ rfl ass₁

/-
## Rewriting rules
-/

theorem skip_same: (skip, s) ⟹ s₁ ↔ s = s₁ := by
  apply Iff.intro <;> intro h
  . cases h; rfl
  . exact h ▸ skip₁

theorem cat_iff: (c₁;;c₂, s) ⟹ s₁ ↔ ∃ t, (c₁, s) ⟹ t ∧ (c₂, t) ⟹ s₁ := by
  apply Iff.intro <;> intro h
  . cases h with | cat₁ t h₁ h₂ =>
      exact ⟨t, ⟨h₁, h₂⟩⟩
  . cases h with | intro w h =>
      exact cat₁ w h.1 h.2

theorem cond_iff: (cond b c d, s) ⟹ t ↔ bif b⇓s then (c, s) ⟹ t else (d, s) ⟹ t := by
  constructor <;> intro h
  . cases h with
    | cond₁ hb hc => exact hb ▸ hc
    | cond₂ hb hc => exact hb ▸ hc
  . cases hb: b⇓s with
    | true => exact cond₁ hb $ (cond_true ((c, s) ⟹ t) _) ▸ hb ▸ h
    | false => exact cond₂ hb $ (cond_false _ ((d, s) ⟹ t)) ▸ hb ▸ h

theorem cond_iff': (cond b c d, s) ⟹ t ↔ (bif b⇓s then c else d, s) ⟹ t := by
  rw [cond_iff]; cases b⇓s <;> simp

theorem loop_iff: (loop b c, s) ⟹ u ↔
  (∃t, b⇓s = true ∧ (c, s) ⟹ t ∧ (loop b c, t) ⟹ u)
  ∨ (b⇓s = false ∧ u = s) := by
  apply Iff.intro <;> intro h
  . cases h with
    | loop₁ t hb hc hw =>
      exact Or.inl ⟨t, ⟨hb, ⟨hc, hw⟩⟩⟩
    | loop₂ hb =>
      exact Or.inr ⟨hb, rfl⟩
  . cases h with
    | inl h =>
      cases h with | intro w h =>
        cases h with | intro hb h =>
            exact loop₁ w hb h.1 h.2
    | inr h =>
      cases h with | intro hb h =>
        exact (symm h) ▸ loop₂ hb

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c d := ∀ s t, (c, s) ⟹ t = (d, s) ⟹ t
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := (Eq.symm $ · · ·)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

theorem skipl: (skip;;c) ≈ c := by
  intro _ _
  apply propext
  constructor
  . intro h; cases h with | cat₁ _ hc hd =>
    exact skip_same.mp hc ▸ hd
  . exact (cat₁ _ skip₁ ·)

theorem skipr: (c;;skip) ≈ c := by
  intro _ _
  apply propext
  constructor
  . intro h; cases h with | cat₁ _ hc hd =>
    exact skip_same.mp hd ▸ hc
  . exact (cat₁ _ · skip₁)

theorem cond_true (h: b ≈ Bexp.tt): cond b c d ≈ c := by
  intro _ _; apply propext; constructor <;> intro h₁
  . cases h₁ with
    | cond₁ => assumption
    | cond₂ hb => rw [h] at hb; contradiction
  . exact cond₁ (h ▸ rfl) h₁

theorem cond_false (h: b ≈ Bexp.ff): cond b c d ≈ d := by
  intro _ _; apply propext; constructor <;> intro h₁
  . cases h₁ with
    | cond₂ => assumption
    | cond₁ hb => rw [h] at hb; contradiction
  . exact cond₂ (h ▸ rfl) h₁

theorem loop_unfold:
  loop b c ≈ cond b (c;;loop b c) skip := by
  intro s t
  apply propext
  constructor <;> intro h
  . cases hb: b⇓s
    . apply cond₂ hb
      cases h
      . rw [hb] at *; contradiction
      . constructor
    . apply cond₁ hb
      cases h
      . constructor <;> assumption
      . rw [hb] at *; contradiction
  . cases hb: b⇓s
    . cases h
      . rw [hb] at *; contradiction
      . rename_i hd; cases hd; apply loop₂; assumption
    . cases h
      . rename_i hc; cases hc; constructor <;> assumption
      . rw [hb] at *; contradiction

/-
## No normalization
-/

theorem loop_tt (hq: b ≈ Bexp.tt):
  ¬((loop b c, s) ⟹ t) := by
  intro h₁
  generalize h₂: (loop b c, s) = ww at h₁
  induction h₁ generalizing s with
  | loop₁ _ _ _ _ _ ih₂ => cases h₂; apply ih₂; rfl
  | loop₂ hb => cases h₂; rw [hq] at hb; contradiction
  | _ => cases h₂

/-
## Determinism
-/

theorem determinist {cs: Config} (h₁: cs ⟹ t) (h₂: cs ⟹ u): t = u :=
  by induction h₁ generalizing u with
  | cat₁ _ _ _ ih₁ ih₂ => cases h₂ with
    | cat₁ _ hc hd => exact ih₂ (ih₁ hc ▸ hd)

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
