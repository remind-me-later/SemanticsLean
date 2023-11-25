import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

inductive ℂ.Nat: ℂ × 𝕊 → 𝕊 → Prop
  | skip₁:
    Nat (skip, s) s

  | ass₁:
    Nat (x ≔ a, s) (s⟦x↦a↓s⟧)

  | cat₁ t (hc: Nat (c, s) t) (hd: Nat (d, t) u):
    Nat (c;;d, s) u

  | ife₁ (hb: b↓s) (hc: Nat (c, s) t):
    Nat (ife b c d, s) t

  | ife₂ {b: 𝔹} (hb: b↓s = false) (hd: Nat (d, s) t):
    Nat (ife b c d, s) t

  | wle₁ u (hb: b↓s) (hc: Nat (c, s) u) (hw: Nat (wle b c, u) t):
    Nat (wle b c, s) t

  | wle₂ {b: 𝔹} (hb: b↓s = false):
    Nat (wle b c, s) s

infix:110 " ⟹ " => ℂ.Nat

theorem ℂ.Nat.demo₁: (⦃x ≔ 5⦄, ⟦⟧) ⟹ ⟦"x"↦5⟧ := ass₁

theorem ℂ.Nat.demo₂:
  (⦃x ≔ 2; if x ≤ 1 {y ≔ 3} else {z ≔ 4}⦄, ⟦⟧) ⟹
  (⟦"x"↦2⟧⟦"z"↦4⟧) := cat₁ _ ass₁ (ife₂ rfl ass₁)

theorem ℂ.Nat.skip_same: (skip, s) ⟹ s₁ ↔ s = s₁ := ⟨(by cases .; rfl), (· ▸ skip₁)⟩

instance Nat.equiv: Setoid ℂ where
  r c d := ∀ s t, (c, s) ⟹ t ↔ (d, s) ⟹ t
  iseqv := {
    refl := by simp
    symm := by intro _ _ h; simp [h]
    trans := by intro _ _ _ h₁ h₂; simp [h₁, h₂]
  }

theorem ℂ.Nat.skipl: (skip;;c) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat₁ _ hc hd =>
    exact skip_same.mp hc ▸ hd
  . exact (cat₁ _ skip₁ ·)

theorem ℂ.Nat.skipr: (c;;skip) ≈ c := by
  intro _ _
  constructor
  . intro h; cases h with | cat₁ _ hc hd =>
    exact skip_same.mp hd ▸ hc
  . exact (cat₁ _ · skip₁)

theorem ℂ.Nat.ife_tt (h: b ≈ 𝔹.tt): ife b c d ≈ c := by
  intro _ _; constructor <;> intro h₁
  . cases h₁ with
    | ife₁ => assumption
    | ife₂ hb => rw [h] at hb; contradiction
  . apply Nat.ife₁ _ h₁
    . apply h

theorem ℂ.Nat.ife_ff (h: b ≈ 𝔹.ff): ife b c d ≈ d := by
  intro _ _; constructor <;> intro h₁
  . cases h₁ with
    | ife₂ => assumption
    | ife₁ hb => rw [h] at hb; contradiction
  . apply Nat.ife₂ _ h₁
    . apply h

theorem ℂ.Nat.wle_unfold:
  wle b c ≈ ife b (c;;wle b c) skip := by
  intro s t
  constructor <;> intro h
  . cases hb: b↓s
    . apply ife₂ hb
      cases h
      . rw [hb] at *; contradiction
      . constructor
    . apply ife₁ hb
      cases h
      . constructor <;> assumption
      . rw [hb] at *; contradiction
  . cases hb: b↓s
    . cases h
      . rw [hb] at *; contradiction
      . rename_i hd; cases hd; apply wle₂; assumption
    . cases h
      . rename_i hc; cases hc; constructor <;> assumption
      . rw [hb] at *; contradiction

theorem ℂ.Nat.ife_ext: (ife b c d, s) ⟹ t ↔ cond (b↓s) ((c, s) ⟹ t) ((d, s) ⟹ t) := by
  constructor <;> intro h <;> cases hb: b↓s <;> simp at *
  . cases h
    simp [hb] at *
    assumption
  . cases h
    assumption
    simp [hb] at *
  . rw [hb] at h
    exact ife₂ hb h
  . rw [hb] at h
    exact ife₁ hb h

-- theorem Nat.ife_ext': (ife b c d, s) ⟹ t ↔ (cond (b↓s) c d, s) ⟹ t := by
--   constructor <;> intro h <;> cases hb: b↓s <;> simp at *
--   . cases h
--     simp [hb] at *
--     assumption
--   . cases h
--     assumption
--     simp [hb] at *
--   . rw [hb] at h
--     exact ife₂ hb h
--   . rw [hb] at h
--     exact ife₁ hb h

theorem ℂ.Nat.wle_iff:
  (wle b c, s) ⟹ u ↔
  (∃t, b↓s ∧ (c, s) ⟹ t ∧ (wle b c, t) ⟹ u)
  ∨ (¬ b↓s ∧ u = s) :=
  by
    apply Iff.intro
    . intro h
      cases h with
      | wle₁ t hb hc hw =>
        apply Or.inl
        apply Exists.intro t
        simp [*]
      | wle₂ hb =>
        apply Or.inr
        simp [*]
    . intro h
      cases h with
      | inl hex =>
        cases hex with
        | intro t h =>
          cases h with
          | intro hB h =>
            cases h with
            | intro hS hwhile =>
              apply wle₁ <;>
                assumption
      | inr h =>
        cases h with
        | intro hb heq =>
          rw [heq]
          apply wle₂
          simp [*]

theorem ℂ.Nat.wle_tt (heqb: b ≈ 𝔹.tt):
  ¬((wle b c, s) ⟹ t) := by
  intro h₁
  generalize h₂: (wle b c, s) = ww at h₁
  induction h₁ generalizing s with
  | wle₁ _ _ _ _ _ ih₂ => cases h₂; apply ih₂; rfl
  | wle₂ hb => cases h₂; rw [heqb] at hb; contradiction
  | _ => cases h₂

theorem ℂ.Nat.determ {cs: ℂ × 𝕊} (h₁: cs ⟹ t) (h₂: cs ⟹ u): t = u :=
  by induction h₁ generalizing u with
  | cat₁ _ _ _ ih₁ ih₂ => cases h₂ with
    | cat₁ _ hc hd => exact ih₂ (ih₁ hc ▸ hd)

  | ife₁ hb _ ih => cases h₂ with
    | ife₁ _ hd => exact ih hd
    | ife₂ hb₁ hd => simp [hb] at hb₁

  | ife₂ hb _ ih => cases h₂ with
    | ife₁ hb₁ hd => simp [hb] at hb₁
    | ife₂ _ hd   => exact ih hd

  | wle₁ _ hb _ _ ih₁ ih₂ => cases h₂ with
    | wle₁ _ _ hc hw => exact ih₂ (ih₁ hc ▸ hw)
    | wle₂ hb₁ => simp [hb] at hb₁

  | wle₂ hb => cases h₂ with
    | wle₁ _ hb₁ => simp [hb] at hb₁
    | wle₂ => rfl

  | _ => cases h₂; rfl
