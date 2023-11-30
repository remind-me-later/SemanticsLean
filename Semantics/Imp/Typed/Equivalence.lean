import Semantics.Imp.Untyped.Natural
import Semantics.Imp.Untyped.Structural
import Semantics.Imp.Untyped.Denote

namespace Com

theorem Structural.from_natural {x: Config} (h: x ⟹ s): x ⇒* (skip, s) := by
  induction h with
  | skip₁ => exact Star.refl
  | ass₁ => exact Star.single Step.ass₁
  | cat₁ _ _ _ ihc ihd => exact Star.cat ihc ihd
  | cond₁ hb _ ih => exact Star.head Step.cond₁ (hb ▸ ih)
  | cond₂ hb _ ih => exact Star.head Step.cond₁ (hb ▸ ih)
  | loop₁ _ hb _ _ ihc ihw =>
    exact Star.head Step.loop₁ $ Star.trans (hb ▸ Star.cat ihc ihw) Star.refl
  | loop₂ hb =>
    exact Star.head Step.loop₁ $ hb ▸ Star.refl

lemma Natural.from_structural_step (h₁: x ⇒ y) (h₂: y ⟹ s): x ⟹ s := by
  induction h₁ generalizing s with
  | ass₁ => exact (skip_iff.mp h₂) ▸ Step.ass₁
  | cat₁ => exact Step.cat₁ _ Step.skip₁ h₂
  | cat₂ _ ih =>
    cases h₂ with
    | cat₁ w hc hd => exact Step.cat₁ w (ih hc) hd
  | cond₁ => rw [cond_iff']; exact h₂
  | loop₁ => rw [loop_unfold, cond_iff']; exact h₂

theorem Natural.from_structural (h: x ⇒* (skip, t)): x ⟹ t := by
  induction h using Structural.Star.head_induction_on with
  | refl => exact Step.skip₁
  | head h _ ht => exact from_structural_step h ht

theorem structural_iff_natural: x ⇒* (skip, t) ↔ x ⟹ t := ⟨Natural.from_structural, Structural.from_natural⟩

theorem denote.from_natural {x: Config} (h: x ⟹ t): (x.2, t) ∈ ⟦x.1⟧ := by
  induction h with
  | skip₁ => exact SRel.mem_id.mpr rfl
  | ass₁  => exact SRel.mem_id.mpr rfl
  | cat₁ t _ _ ih₁ ih₂ => exact ⟨t, ⟨ih₁, ih₂⟩⟩
  | cond₁ hb _ ih => exact Or.inl ⟨ih, hb⟩
  | cond₂ hb _ ih => exact Or.inr ⟨ih, hb⟩
  | loop₁ t hb _ _ ih₁ ih₂ => exact loop_unfold ▸ Or.inl ⟨⟨t, ⟨ih₁, ih₂⟩⟩, hb⟩
  | loop₂ hb => exact loop_unfold ▸ Or.inr ⟨rfl, hb⟩

theorem Natural.from_denote (h: (s, t) ∈ ⟦c⟧): (c, s) ⟹ t := by
  revert h
  induction c generalizing s t with
  | skip => intro h; cases h; exact Step.skip₁
  | ass => intro h; simp [denote] at h; exact h ▸ Step.ass₁
  | cat _ _ ih₁ ih₂ =>
    intro h
    cases h with | intro w h =>
      exact Step.cat₁ w (ih₁ h.left) (ih₂ h.right)
  | cond _ _ _ ih₁ ih₂ =>
    intro h
    cases h with
    | inl h =>
      cases h with | intro h hb =>
        exact Step.cond₁ hb (ih₁ h)
    | inr h =>
      cases h with | intro h hb =>
        exact Step.cond₂ hb (ih₂ h)
  | loop b c ih =>
    suffices ⟦loop b c⟧ ⊆ {s | (loop b c, s.1) ⟹ s.2} by apply this
    apply OrderHom.lfp_le
    intro ss h
    cases ss with | mk =>
      cases h with
      | inl h =>
        cases h with | intro h hb =>
          cases h with | intro w h =>
            exact Step.loop₁ w hb (ih h.left) h.right
      | inr h =>
        cases h with | intro hq hb =>
          simp at hq
          exact hq ▸ Step.loop₂ hb

theorem natural_iff_denote: (s, t) ∈ ⟦c⟧ ↔ (c, s) ⟹ t := ⟨Natural.from_denote, denote.from_natural⟩

end Com
