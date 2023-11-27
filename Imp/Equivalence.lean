import Imp.Natural
import Imp.Structural
import Imp.Denot

theorem Com.Star.of_Nat {x: Com × State} (h: x ⟹ s): x ⇒* (skip, s) := by
  induction h with
  | skip₁ => exact refl
  | ass₁ => exact single Step.ass₁
  | cat₁ _ _ _ ihc ihd => exact Star.cat ihc ihd
  | cond₁ hb _ ih => exact head Step.cond₁ (hb ▸ ih)
  | cond₂ hb _ ih => exact head Step.cond₁ (hb ▸ ih)
  | wle₁ _ hb _ _ ihc ihw =>
    exact head Step.wle₁ (head Step.cond₁ (hb ▸ Star.cat ihc ihw))
  | wle₂ hb =>
    exact head Step.wle₁ (head ((Step.cond_false hb).mpr rfl) refl)

lemma Com.Nat.of_Step (h₁: x ⇒ y) (h₂: y ⟹ s): x ⟹ s := by
  induction h₁ generalizing s with
  | ass₁ => cases h₂; exact ass₁
  | cat₁ => exact cat₁ _ skip₁ h₂
  | cat₂ _ ih =>
    cases h₂ with
    | cat₁ w hc hd => exact cat₁ w (ih hc) hd
  | cond₁ => exact cond_ext''.mpr h₂
  | wle₁ => rw [wle_unfold]; exact h₂

theorem Com.Nat.of_Star (h: x ⇒* (skip, t)): x ⟹ t := by
  induction h using Star.head_induction_on with
  | refl => exact skip₁
  | head x x' ht => cases x' <;> exact of_Step x ht

theorem Com.Star_iff_Nat: x ⇒* (skip, t) ↔ x ⟹ t := ⟨Nat.of_Star, Star.of_Nat⟩

theorem Com.denot.of_Nat {x: Com × State} (h: x ⟹ t): (x.2, t) ∈ ⟦x.1⟧ := by
  induction h with
  | skip₁ => rfl
  | ass₁  => rfl
  | cat₁ t _ _ ih₁ ih₂ =>
    exact ⟨t, ⟨ih₁, ih₂⟩⟩
  | cond₁ hb _ ih =>
    simp [denot]
    exact Or.inl ⟨ih, hb⟩
  | cond₂ hb _ ih =>
    simp [denot]
    exact Or.inr ⟨ih, hb⟩
  | wle₁ t hb _ _ ih₁ ih₂ =>
    rw [wle_unfold]
    simp [denot]
    exact Or.inl ⟨⟨t, ⟨ih₁, ih₂⟩⟩, hb⟩
  | wle₂ hb =>
    rw [wle_unfold]
    simp [denot]
    exact Or.inr hb

theorem Com.Nat.of_denot (h: (s, t) ∈ ⟦c⟧): (c, s) ⟹ t := by
  revert h
  induction c generalizing s t with
  | skip => intro h; cases h; exact skip₁
  | ass => intro h; simp [denot] at h; exact h ▸ ass₁
  | cat _ _ ih₁ ih₂ =>
    intro h
    cases h with | intro w h =>
      exact cat₁ w (ih₁ h.left) (ih₂ h.right)
  | cond _ _ _ ih₁ ih₂ =>
    intro h
    cases h with
    | inl h =>
      simp at *
      cases h with | intro h hb =>
        exact cond₁ hb (ih₁ h)
    | inr h =>
      simp at *
      cases h with | intro h hb =>
        exact cond₂ hb (ih₂ h)
  | wle b c ih =>
    suffices ⟦wle b c⟧ ≤ {s | (wle b c, s.1) ⟹ s.2} by apply this
    apply OrderHom.lfp_le
    intro ss h
    cases ss with | mk =>
      cases h with
      | inl h =>
        cases h with | intro h hb =>
          cases h with | intro w h =>
            simp at *
            exact wle₁ w hb (ih h.left) h.right
      | inr h =>
        cases h with | intro hq hb =>
          simp at *
          exact hq ▸ wle₂ hb

theorem Com.Nat_iff_denot: (s, t) ∈ ⟦c⟧ ↔ (c, s) ⟹ t := ⟨Nat.of_denot, denot.of_Nat⟩
