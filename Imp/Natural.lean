import Imp.Bexp

inductive Com.Nat: Com × State → State → Prop
  | skip₁:
    Nat (skip, s) s

  | ass₁:
    Nat (ass x a, s) (s⟦x↦a↓s⟧)

  | cat₁ t
    (hc: Nat (c, s) t) (hd: Nat (d, t) u):
    Nat (c;;d, s) u

  | cond₁ {b: Bexp}
    (hb: b↓s = true) (hc: Nat (c, s) t):
    Nat (cond b c d, s) t

  | cond₂ {b: Bexp}
    (hb: b↓s = false) (hd: Nat (d, s) t):
    Nat (cond b c d, s) t

  | wle₁ {b: Bexp} u
    (hb: b↓s = true) (hc: Nat (c, s) u) (hw: Nat (wle b c, u) t):
    Nat (wle b c, s) t

  | wle₂ {b: Bexp}
    (hb: b↓s = false):
    Nat (wle b c, s) s

infix:110 " ⟹ " => Com.Nat

theorem Com.Nat.demo₁: (⦃x = 5⦄, ⟦⟧) ⟹ ⟦"x"↦5⟧ := ass₁

theorem Com.Nat.demo₂:
  (⦃x = 2; if x <= 1 {y = 3} else {z = 4}⦄, ⟦⟧) ⟹
  (⟦"x"↦2⟧⟦"z"↦4⟧) := cat₁ _ ass₁ (cond₂ rfl ass₁)

theorem Com.Nat.skip_same: (skip, s) ⟹ s₁ ↔ s = s₁ := ⟨(by cases .; rfl), (· ▸ skip₁)⟩

instance Com.Nat.equiv: Setoid Com where
  r c d := ∀ s t, (c, s) ⟹ t = (d, s) ⟹ t
  iseqv := {
    refl := λ _ _ _ ↦ Eq.refl _
    symm := λ h s n ↦ Eq.symm (h s n)
    trans := λ h₁ h₂ x n ↦ (h₁ x n) ▸ (h₂ x n)
  }

theorem Com.Nat.skipl: (skip;;c) ≈ c := by
  intro _ _
  apply propext
  constructor
  . intro h; cases h with | cat₁ _ hc hd =>
    exact skip_same.mp hc ▸ hd
  . exact (cat₁ _ skip₁ ·)

theorem Com.Nat.skipr: (c;;skip) ≈ c := by
  intro _ _
  apply propext
  constructor
  . intro h; cases h with | cat₁ _ hc hd =>
    exact skip_same.mp hd ▸ hc
  . exact (cat₁ _ · skip₁)

theorem Com.Nat.cond_tt (h: b ≈ Bexp.tt): cond b c d ≈ c := by
  intro _ _; apply propext; constructor <;> intro h₁
  . cases h₁ with
    | cond₁ => assumption
    | cond₂ hb => rw [h] at hb; contradiction
  . exact Nat.cond₁ (h ▸ rfl) h₁

theorem Com.Nat.cond_ff (h: b ≈ Bexp.ff): cond b c d ≈ d := by
  intro _ _; apply propext; constructor <;> intro h₁
  . cases h₁ with
    | cond₂ => assumption
    | cond₁ hb => rw [h] at hb; contradiction
  . exact Nat.cond₂ (h ▸ rfl) h₁

theorem Com.Nat.wle_unfold:
  wle b c ≈ cond b (c;;wle b c) skip := by
  intro s t
  apply propext
  constructor <;> intro h
  . cases hb: b↓s
    . apply cond₂ hb
      cases h
      . rw [hb] at *; contradiction
      . constructor
    . apply cond₁ hb
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

theorem Com.Nat.cond_ext: (cond b c d, s) ⟹ t ↔ bif b↓s then (c, s) ⟹ t else (d, s) ⟹ t := by
  constructor <;> intro h <;> cases hb: b↓s <;> simp at *
  . cases h
    simp [hb] at *
    assumption
  . cases h
    assumption
    simp [hb] at *
  . rw [hb] at h
    exact cond₂ hb h
  . rw [hb] at h
    exact cond₁ hb h

theorem Com.Nat.cond_ext': (cond b c d, s) ⟹ t ↔ (bif b↓s then c else d, s) ⟹ t := by
  rw [cond_ext]; cases b↓s <;> simp

theorem Com.Nat.cond_ext'': (cond b c d, s) ⟹ t ↔ (bif b↓s then (c, s) else (d, s)) ⟹ t := by
  rw [cond_ext]; cases b↓s <;> simp

theorem Com.Nat.wle_iff:
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

theorem Com.Nat.wle_tt (heqb: b ≈ Bexp.tt):
  ¬((wle b c, s) ⟹ t) := by
  intro h₁
  generalize h₂: (wle b c, s) = ww at h₁
  induction h₁ generalizing s with
  | wle₁ _ _ _ _ _ ih₂ => cases h₂; apply ih₂; rfl
  | wle₂ hb => cases h₂; rw [heqb] at hb; contradiction
  | _ => cases h₂

theorem Com.Nat.determ {cs: Com × State} (h₁: cs ⟹ t) (h₂: cs ⟹ u): t = u :=
  by induction h₁ generalizing u with
  | cat₁ _ _ _ ih₁ ih₂ => cases h₂ with
    | cat₁ _ hc hd => exact ih₂ (ih₁ hc ▸ hd)

  | cond₁ hb _ ih => cases h₂ with
    | cond₁ _ hd => exact ih hd
    | cond₂ hb₁ hd => simp [hb] at hb₁

  | cond₂ hb _ ih => cases h₂ with
    | cond₁ hb₁ hd => simp [hb] at hb₁
    | cond₂ _ hd   => exact ih hd

  | wle₁ _ hb _ _ ih₁ ih₂ => cases h₂ with
    | wle₁ _ _ hc hw => exact ih₂ (ih₁ hc ▸ hw)
    | wle₂ hb₁ => simp [hb] at hb₁

  | wle₂ hb => cases h₂ with
    | wle₁ _ hb₁ => simp [hb] at hb₁
    | wle₂ => rfl

  | _ => cases h₂; rfl
