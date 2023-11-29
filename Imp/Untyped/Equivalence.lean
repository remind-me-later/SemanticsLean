import Imp.Untyped.Natural
import Imp.Untyped.Structural
import Imp.Untyped.Denote

theorem Com.Star.of_Nat {x: Config} (h: x ⟹ s): x ⇒* (skip, s) := by
  induction h with
  | skip₁ => exact refl
  | ass₁ => exact single Step.ass₁
  | cat₁ _ _ _ ihc ihd => exact cat ihc ihd
  | cond₁ hb _ ih => exact head Step.cond₁ (hb ▸ ih)
  | cond₂ hb _ ih => exact head Step.cond₁ (hb ▸ ih)
  | loop₁ _ hb _ _ ihc ihw =>
    exact head Step.loop₁ $ trans (hb ▸ cat ihc ihw) refl
  | loop₂ hb =>
    exact head Step.loop₁ $ hb ▸ refl

lemma Com.Natural.of_Step (h₁: x ⇒ y) (h₂: y ⟹ s): x ⟹ s := by
  induction h₁ generalizing s with
  | ass₁ => exact (skip_iff.mp h₂) ▸ ass₁
  | cat₁ => exact cat₁ _ skip₁ h₂
  | cat₂ _ ih =>
    cases h₂ with
    | cat₁ w hc hd => exact cat₁ w (ih hc) hd
  | cond₁ => rw [cond_iff']; exact h₂
  | loop₁ => rw [loop_unfold, cond_iff']; exact h₂

theorem Com.Natural.of_Star (h: x ⇒* (skip, t)): x ⟹ t := by
  induction h using Star.head_induction_on with
  | refl => exact skip₁
  | head x x' ht => cases x' <;> exact of_Step x ht

theorem Com.Star_iff_Nat: x ⇒* (skip, t) = x ⟹ t := propext ⟨Natural.of_Star, Star.of_Nat⟩

theorem Com.denote.of_Nat {x: Config} (h: x ⟹ t): (x.2, t) ∈ ⟦x.1⟧ := by
  induction h with
  | skip₁ => exact SRel.mem_id.mpr rfl
  | ass₁  => exact SRel.mem_id.mpr rfl
  | cat₁ t _ _ ih₁ ih₂ => exact ⟨t, ⟨ih₁, ih₂⟩⟩
  | cond₁ hb _ ih => exact Or.inl ⟨ih, hb⟩
  | cond₂ hb _ ih => exact Or.inr ⟨ih, hb⟩
  | loop₁ t hb _ _ ih₁ ih₂ => exact loop_unfold ▸ Or.inl ⟨⟨t, ⟨ih₁, ih₂⟩⟩, hb⟩
  | loop₂ hb => exact loop_unfold ▸ Or.inr ⟨rfl, hb⟩

theorem Com.Natural.of_denote (h: (s, t) ∈ ⟦c⟧): (c, s) ⟹ t := by
  revert h
  induction c generalizing s t with
  | skip => intro h; cases h; exact skip₁
  | ass => intro h; simp [denote] at h; exact h ▸ ass₁
  | cat _ _ ih₁ ih₂ =>
    intro h
    cases h with | intro w h =>
      exact cat₁ w (ih₁ h.left) (ih₂ h.right)
  | cond _ _ _ ih₁ ih₂ =>
    intro h
    cases h with
    | inl h =>
      cases h with | intro h hb =>
        exact cond₁ hb (ih₁ h)
    | inr h =>
      cases h with | intro h hb =>
        exact cond₂ hb (ih₂ h)
  | loop b c ih =>
    suffices ⟦loop b c⟧ ⊆ {s | (loop b c, s.1) ⟹ s.2} by apply this
    apply OrderHom.lfp_le
    intro ss h
    cases ss with | mk =>
      cases h with
      | inl h =>
        cases h with | intro h hb =>
          cases h with | intro w h =>
            exact loop₁ w hb (ih h.left) h.right
      | inr h =>
        cases h with | intro hq hb =>
          simp at hq
          exact hq ▸ loop₂ hb

theorem Com.Nat_iff_denote: ((s, t) ∈ ⟦c⟧) = (c, s) ⟹ t := propext ⟨Natural.of_denote, denote.of_Nat⟩
