import Semantics.Imp.Natural
import Semantics.Imp.Structural
import Semantics.Imp.Denotational

namespace Com

theorem Structural.from_natural {c: Com} (h: w ⊢ c ⟹ s): (c, w) ⇒* (skip, s) := by
  induction h with
  | skip => exact RTL.refl
  | ass => exact RTL.single step.ass
  | cat _ _ _ ihc ihd => exact star.cat ihc ihd
  | cond_true hb _ ih => exact RTL.head step.cond (hb ▸ ih)
  | cond_false hb _ ih => exact RTL.head step.cond (hb ▸ ih)
  | loop_true _ hb _ _ ihc ihw =>
    exact RTL.head step.loop $ RTL.trans (hb ▸ star.cat ihc ihw) RTL.refl
  | loop_false hb =>
    exact RTL.head step.loop $ hb ▸ RTL.refl

theorem Natural.from_structural_step (h₁: x ⇒ y) (h₂: y.2 ⊢ y.1  ⟹ s): x.2 ⊢ x.1 ⟹ s := by
  induction h₁ generalizing s with
  | ass => exact (skip_iff.mp h₂) ▸ step.ass
  | cat_skip => exact step.cat _ step.skip h₂
  | cat_step _ ih =>
    cases h₂ with
    | cat w hc hd => exact step.cat w (ih hc) hd
  | cond => rw [cond_iff']; exact h₂
  | _ => rw [loop_unfold, cond_iff']; exact h₂

theorem Natural.from_structural (h: x ⇒* (skip, t)): x.2 ⊢ x.1 ⟹ t := by
  induction h using RTL.head_induction_on with
  | refl => exact step.skip
  | head h _ ht => exact from_structural_step h ht

theorem structural_iff_natural: (c, s) ⇒* (skip, t) ↔ (s ⊢ c ⟹ t) := ⟨Natural.from_structural, Structural.from_natural⟩

theorem denote.from_natural {c: Com} (h: s ⊢ c ⟹ t): (s, t) ∈ ⟦c⟧ := by
  induction h with
  | skip => exact SRel.mem_id.mpr rfl
  | ass  => exact SRel.mem_id.mpr rfl
  | cat t _ _ ih₁ ih₂ => exact ⟨t, ⟨ih₁, ih₂⟩⟩
  | cond_true hb _ ih => exact Or.inl ⟨ih, hb⟩
  | cond_false hb _ ih =>
      apply Or.inr
      rw [
        Set.mem_diff,
        Set.mem_comprehend,
        hb,
        Bool.false_eq_true,
        not_false_eq_true,
        and_true
      ]
      exact ih
  | loop_true t hb _ _ ih₁ ih₂ => exact loop_unfold ▸ Or.inl ⟨⟨t, ⟨ih₁, ih₂⟩⟩, hb⟩
  | loop_false hb =>
      rw [loop_unfold]
      apply Or.inr
      rw [
        Set.mem_diff,
        Set.mem_comprehend,
        hb,
        Bool.false_eq_true,
        not_false_eq_true,
        and_true
      ]
      rfl

theorem Natural.from_denote (h: (s, t) ∈ ⟦c⟧): s ⊢ c ⟹ t := by
  revert h
  induction c generalizing s t with
  | skip => intro h; cases h; exact step.skip
  | ass =>
    intro h
    rw [denote.eq_def, Set.mem_comprehend] at h
    simp at h
    exact h ▸ step.ass
  | cat _ _ ih₁ ih₂ =>
    intro h
    cases h with | intro w h =>
      exact step.cat w (ih₁ h.left) (ih₂ h.right)
  | cond _ _ _ ih₁ ih₂ =>
    intro h
    cases h with
    | inl h =>
      cases h with | intro h hb =>
        exact step.cond_true hb (ih₁ h)
    | inr h =>
      cases h with | intro h hb =>
        simp [Set.mem_comprehend] at hb
        exact step.cond_false hb (ih₂ h)
  | _ b c ih =>
    suffices ⟦while b loop c end⟧ ⊆ {s | s.1 ⊢ while b loop c end ⟹ s.2} by apply this
    apply Fix.lfp_le
    intro ss h
    cases ss with | mk =>
      cases h with
      | inl h =>
        cases h with | intro h hb =>
          cases h with | intro w h =>
            exact step.loop_true w hb (ih h.left) h.right
      | inr h =>
        cases h with | intro hq hb =>
          simp [Set.mem_comprehend] at hb
          rw [SRel.mem_id] at hq
          exact hq ▸ step.loop_false hb

theorem natural_iff_denote: (s, t) ∈ ⟦c⟧ ↔ (s ⊢ c ⟹ t) := ⟨Natural.from_denote, denote.from_natural⟩

end Com
