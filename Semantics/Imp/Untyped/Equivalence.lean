import Semantics.Imp.Untyped.Natural
import Semantics.Imp.Untyped.Structural
import Semantics.Imp.Untyped.Denote

namespace Com

theorem Structural.from_natural {c: Com} (h: w ⊢ c ⟹ s): (c, w) ⇒* (skip, s) := by
  induction h with
  | skip => exact Relation.ReflTransGen.refl
  | ass => exact Relation.ReflTransGen.single step.ass
  | cat _ _ _ ihc ihd => exact star.cat ihc ihd
  | cond₁ hb _ ih => exact Relation.ReflTransGen.head step.cond (hb ▸ ih)
  | cond₂ hb _ ih => exact Relation.ReflTransGen.head step.cond (hb ▸ ih)
  | loop₁ _ hb _ _ ihc ihw =>
    exact Relation.ReflTransGen.head step.loop $ Relation.ReflTransGen.trans (hb ▸ star.cat ihc ihw) Relation.ReflTransGen.refl
  | loop₂ hb =>
    exact Relation.ReflTransGen.head step.loop $ hb ▸ Relation.ReflTransGen.refl

lemma Natural.from_structural_step (h₁: x ⇒ y) (h₂: y.2 ⊢ y.1  ⟹ s): x.2 ⊢ x.1 ⟹ s := by
  induction h₁ generalizing s with
  | ass => exact (skip_iff.mp h₂) ▸ step.ass
  | cat₁ => exact step.cat _ step.skip h₂
  | cat₂ _ ih =>
    cases h₂ with
    | cat w hc hd => exact step.cat w (ih hc) hd
  | cond => rw [cond_iff']; exact h₂
  | loop => rw [loop_unfold, cond_iff']; exact h₂

theorem Natural.from_structural (h: x ⇒* (skip, t)): x.2 ⊢ x.1 ⟹ t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact step.skip
  | head h _ ht => exact from_structural_step h ht

theorem structural_iff_natural: (c, s) ⇒* (skip, t) ↔ (s ⊢ c ⟹ t) := ⟨Natural.from_structural, Structural.from_natural⟩

theorem denote.from_natural {c: Com} (h: s ⊢ c ⟹ t): (s, t) ∈ ⟦c⟧ := by
  induction h with
  | skip => exact SRel.mem_id.mpr rfl
  | ass  => exact SRel.mem_id.mpr rfl
  | cat t _ _ ih₁ ih₂ => exact ⟨t, ⟨ih₁, ih₂⟩⟩
  | cond₁ hb _ ih => exact Or.inl ⟨ih, hb⟩
  | cond₂ hb _ ih => exact Or.inr ⟨ih, hb⟩
  | loop₁ t hb _ _ ih₁ ih₂ => exact loop_unfold ▸ Or.inl ⟨⟨t, ⟨ih₁, ih₂⟩⟩, hb⟩
  | loop₂ hb => exact loop_unfold ▸ Or.inr ⟨rfl, hb⟩

theorem Natural.from_denote (h: (s, t) ∈ ⟦c⟧): s ⊢ c ⟹ t := by
  revert h
  induction c generalizing s t with
  | skip => intro h; cases h; exact step.skip
  | ass => intro h; simp [denote] at h; exact h ▸ step.ass
  | cat _ _ ih₁ ih₂ =>
    intro h
    cases h with | intro w h =>
      exact step.cat w (ih₁ h.left) (ih₂ h.right)
  | cond _ _ _ ih₁ ih₂ =>
    intro h
    cases h with
    | inl h =>
      cases h with | intro h hb =>
        exact step.cond₁ hb (ih₁ h)
    | inr h =>
      cases h with | intro h hb =>
        exact step.cond₂ hb (ih₂ h)
  | loop b c ih =>
    suffices ⟦loop b c⟧ ⊆ {s | s.1 ⊢ loop b c ⟹ s.2} by apply this
    apply OrderHom.lfp_le
    intro ss h
    cases ss with | mk =>
      cases h with
      | inl h =>
        cases h with | intro h hb =>
          cases h with | intro w h =>
            exact step.loop₁ w hb (ih h.left) h.right
      | inr h =>
        cases h with | intro hq hb =>
          simp at hq
          exact hq ▸ step.loop₂ hb

theorem natural_iff_denote: (s, t) ∈ ⟦c⟧ ↔ (s ⊢ c ⟹ t) := ⟨Natural.from_denote, denote.from_natural⟩

end Com
