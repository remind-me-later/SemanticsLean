import Semantics.Imp.Natural
import Semantics.Imp.Structural
import Semantics.Imp.Denotational

namespace Com

theorem Structural.from_natural
  (hconf: conf ==>ₙ s₂): conf =>ₛ* (skip₁, s₂) := by
  induction hconf with
  | skipₙ => exact RTL.refl
  | assₙ => exact RTL.single small_step.assₛ
  | catₙ _ _ _ ihc₁ ihc₂ => exact star.cat ihc₁ ihc₂
  | if₁ₙ hb _ ih => exact RTL.head small_step.ifₛ (hb ▸ ih)
  | if₀ₙ hb _ ih => exact RTL.head small_step.ifₛ (hb ▸ ih)
  | while₁ₙ _ hb _ _ ihc ihw =>
    exact RTL.head small_step.whileₛ $ RTL.trans (hb ▸ star.cat ihc ihw) RTL.refl
  | while₀ₙ hb =>
    exact RTL.head small_step.whileₛ $ hb ▸ RTL.refl

theorem Natural.from_structural_step
  (hconf₁: conf₁ =>ₛ conf₂) (hconf₂: conf₂ ==>ₙ s₂): conf₁ ==>ₙ s₂ := by
  induction hconf₁ generalizing s₂ with
  | assₛ => exact (skip_eq.mp hconf₂) ▸ big_step.assₙ
  | cat₀ₛ => exact big_step.catₙ _ big_step.skipₙ hconf₂
  | catₙₛ _ ih =>
    match hconf₂ with
    | big_step.catₙ s₂ hc₁ hc₂ => exact big_step.catₙ s₂ (ih hc₁) hc₂
  | ifₛ => exact if_eq' ▸ hconf₂
  | whileₛ => rw [loop_unfold]; exact if_eq' ▸ hconf₂

theorem Natural.from_structural
  (hconf: conf =>ₛ* (skip₁, s₂)): conf ==>ₙ s₂ := by
  induction hconf using RTL.head_induction_on with
  | refl => exact big_step.skipₙ
  | head hsingle _ hs₂ => exact from_structural_step hsingle hs₂

theorem structural_eq_natural:
  ((c₁, s₁) =>ₛ* (skip₁, s₂)) = ((c₁, s₁) ==>ₙ s₂) :=
  propext ⟨Natural.from_structural, Structural.from_natural⟩

theorem denote.from_natural
  (hconf: conf ==>ₙ s₃): (conf.2, s₃) ∈ ⟦conf.1⟧ := by
  induction hconf with
  | skipₙ => exact SFun.mem_id.mpr rfl
  | assₙ  => exact SFun.mem_id.mpr rfl
  | catₙ s₂ _ _ ih₁ ih₂ => exact ⟨s₂, ih₁, ih₂⟩
  | if₁ₙ hb _ ih => exact Or.inl ⟨ih, hb⟩
  | if₀ₙ hb _ ih =>
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hb,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      exact ih
  | while₁ₙ s₂ hb _ _ ih₁ ih₂ =>
    exact while_unfold ▸ Or.inl ⟨⟨s₂, ih₁, ih₂⟩, hb⟩
  | while₀ₙ hb =>
      rw [while_unfold]
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hb,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      rfl

theorem Natural.from_denote
  (hmem: (s₁, s₃) ∈ ⟦c⟧): (c, s₁) ==>ₙ s₃ := by
  revert hmem
  induction c generalizing s₁ s₃ with
  | skip₁ =>
    intro hmp
    rw [denote, SFun.mem_id] at hmp
    exact hmp ▸ big_step.skipₙ
  | ass₁ =>
    intro hmp
    rw [denote.eq_def, Set.mem_comprehend] at hmp
    simp only at hmp
    exact hmp ▸ big_step.assₙ
  | cat₁ _ _ ih₁ ih₂ =>
    intro ⟨s₂, h₁, h₂⟩
    exact big_step.catₙ s₂ (ih₁ h₁) (ih₂ h₂)
  | if₁ _ _ _ ih₁ ih₂ =>
    intro hmp
    match hmp with
    | Or.inl ⟨h₁, hb⟩ =>
      exact big_step.if₁ₙ hb (ih₁ h₁)
    | Or.inr ⟨h₁, hb⟩ =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hb
      exact big_step.if₀ₙ hb (ih₂ h₁)
  | while₁ b c ih =>
    suffices
      ⟦while b loop c end⟧ ⊆ {(s₁, s₃) | (while b loop c end, s₁) ==>ₙ s₃} by
      apply this

    apply Fix.lfp_le
    intro ⟨_, _⟩ hmp
    match hmp with
    | Or.inl ⟨⟨s₂, h₁, h₂⟩, hb⟩ =>
      exact big_step.while₁ₙ s₂ hb (ih h₁) h₂
    | Or.inr ⟨hid, hb⟩ =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hb
      rw [SFun.mem_id] at hid
      exact hid ▸ big_step.while₀ₙ hb

theorem natural_eq_denote: ((s₁, s₂) ∈ ⟦c⟧) = ((c, s₁) ==>ₙ s₂) :=
  propext ⟨Natural.from_denote, denote.from_natural⟩

theorem structural_eq_denote:
  ((c, s₁) =>ₛ* (skip₁, s₂)) = ((s₁, s₂) ∈ ⟦c⟧) :=
  by rw [structural_eq_natural, natural_eq_denote]

end Com
