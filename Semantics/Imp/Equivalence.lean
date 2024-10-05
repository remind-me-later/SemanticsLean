import Semantics.Imp.Natural
import Semantics.Imp.Structural
import Semantics.Imp.Denotational

namespace Com

theorem Structural.from_natural
  (h: p ⟹ s): p ⇒* (skip₁, s) := by
  induction h with
  | skipₙ => exact RTL.refl
  | assₙ => exact RTL.single step.assₛ
  | catₙ _ _ _ ihc ihd => exact star.cat ihc ihd
  | if₁ₙ hb _ ih => exact RTL.head step.ifₛ (hb ▸ ih)
  | if₀ₙ hb _ ih => exact RTL.head step.ifₛ (hb ▸ ih)
  | while₁ₙ _ hb _ _ ihc ihw =>
    exact RTL.head step.whileₛ $ RTL.trans (hb ▸ star.cat ihc ihw) RTL.refl
  | while₀ₙ hb =>
    exact RTL.head step.whileₛ $ hb ▸ RTL.refl

theorem Natural.from_structural_step
  (h₁: x ⇒ y) (h₂: y ⟹ s): x ⟹ s := by
  induction h₁ generalizing s with
  | assₛ => exact (skip_eq.mp h₂) ▸ step.assₙ
  | cat₀ₛ => exact step.catₙ _ step.skipₙ h₂
  | catₙₛ _ ih =>
    match h₂ with
    | step.catₙ w hc hd => exact step.catₙ w (ih hc) hd
  | ifₛ => exact if_eq' ▸ h₂
  | whileₛ => rw [loop_unfold]; exact if_eq' ▸ h₂

theorem Natural.from_structural
  (h: x ⇒* (skip₁, t)): x ⟹ t := by
  induction h using RTL.head_induction_on with
  | refl => exact step.skipₙ
  | head h _ ht => exact from_structural_step h ht

theorem structural_eq_natural:
  ((c, s) ⇒* (skip₁, t)) = ((c, s) ⟹ t) :=
  propext ⟨Natural.from_structural, Structural.from_natural⟩

theorem denote.from_natural
  (h: p ⟹ t): (p.2, t) ∈ ⟦p.1⟧ := by
  induction h with
  | skipₙ => exact SFun.mem_id.mpr rfl
  | assₙ  => exact SFun.mem_id.mpr rfl
  | catₙ t _ _ ih₁ ih₂ => exact ⟨t, ih₁, ih₂⟩
  | if₁ₙ hb _ ih => exact Or.inl ⟨ih, hb⟩
  | if₀ₙ hb _ ih =>
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hb,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      exact ih
  | while₁ₙ t hb _ _ ih₁ ih₂ =>
    exact while_unfold ▸ Or.inl ⟨⟨t, ih₁, ih₂⟩, hb⟩
  | while₀ₙ hb =>
      rw [while_unfold]
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hb,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      rfl

theorem Natural.from_denote (h: (s, t) ∈ ⟦c⟧): (c, s) ⟹ t := by
  revert h
  induction c generalizing s t with
  | skip₁ =>
    intro h
    rw [denote, SFun.mem_id] at h
    exact h ▸ step.skipₙ
  | ass₁ =>
    intro h
    rw [denote.eq_def, Set.mem_comprehend] at h
    simp only at h
    exact h ▸ step.assₙ
  | cat₁ _ _ ih₁ ih₂ =>
    intro ⟨w, h1, h2⟩
    exact step.catₙ w (ih₁ h1) (ih₂ h2)
  | if₁ _ _ _ ih₁ ih₂ =>
    intro h
    match h with
    | Or.inl ⟨h, hb⟩ =>
      exact step.if₁ₙ hb (ih₁ h)
    | Or.inr ⟨h, hb⟩ =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hb
      exact step.if₀ₙ hb (ih₂ h)
  | while₁ b c ih =>
    suffices
      ⟦while b loop c end⟧ ⊆ {s | (while b loop c end, s.1) ⟹ s.2} by
      apply this

    apply Fix.lfp_le
    intro ⟨_, _⟩ h
    match h with
    | Or.inl ⟨⟨w, h1, h2⟩, hb⟩ =>
      exact step.while₁ₙ w hb (ih h1) h2
    | Or.inr ⟨hq, hb⟩ =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hb
      rw [SFun.mem_id] at hq
      exact hq ▸ step.while₀ₙ hb

theorem natural_eq_denote: ((s, t) ∈ ⟦c⟧) = ((c, s) ⟹ t) :=
  propext ⟨Natural.from_denote, denote.from_natural⟩

end Com
