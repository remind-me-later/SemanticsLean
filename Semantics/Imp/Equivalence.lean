import Semantics.Imp.BigStep
import Semantics.Imp.SmallStep
import Semantics.Imp.Denotational

namespace Com

theorem SmallStep.from_natural {x: Com × State}
  (h: x ==> s'): x ~>* (∅, s') := by
  induction h with
  | skip => exact .refl
  | ass => exact .single ass
  | cat _ _ _ ihcatl ihcatr => exact star.cat ihcatl ihcatr
  | ifTrue hc _ ih => exact .head ifElse (hc ▸ ih)
  | ifFalse hc _ ih => exact .head ifElse (hc ▸ ih)
  | whileTrue _ hc _ _ ihc ihw =>
    exact .head whileLoop (.trans (hc ▸ star.cat ihc ihw) .refl)
  | whileFalse hc =>
    exact .head whileLoop (hc ▸ .refl)

theorem BigStep.from_structural_step
  (h: x ~> x') (h': x' ==> s'): x ==> s' := by
  induction h generalizing s' with
  | ass => exact (skip_eq.mp h') ▸ ass
  | skipCat => exact cat _ skip h'
  | cat _ ih => match h' with
    | cat s' hcatl hccatr => exact cat s' (ih hcatl) hccatr
  | ifElse => rw [if_eq']; exact h'
  | whileLoop => rw [loop_unfold, if_eq']; exact h'

theorem BigStep.from_structural (h: x ~>* (∅, s')): x ==> s' := by
  induction h using ReflTrans.head_induction_on with
  | refl => exact skip
  | head hsingle _ hs' => exact from_structural_step hsingle hs'

theorem structural_eq_natural: (c, s) ~>* (∅, s') ↔ (c, s) ==> s' :=
  ⟨BigStep.from_structural, SmallStep.from_natural⟩

theorem denote.from_natural {x: Com × State}
  (h: x ==> s''): (x.2, s'') ∈ ⟦x.1⟧ := by
  induction h with
  | skip => exact rfl
  | ass  => exact rfl
  | cat s' _ _ ihcatl ihcatr => exact ⟨s', ihcatl, ihcatr⟩
  | ifTrue hc _ ih => exact .inl ⟨ih, hc⟩
  | ifFalse hc _ ih =>
    exact .inr ⟨ih, (absurd . (Bool.not_eq_true _ ▸ hc))⟩
  | whileTrue s' hc _ _ ihwhilestep ihwhilerest =>
    exact Denotational.while_unfold ▸
      .inl ⟨⟨s', ihwhilestep, ihwhilerest⟩, hc⟩
  | whileFalse hc =>
    exact Denotational.while_unfold ▸
      .inr ⟨denote.eq_1 ▸ rfl, (absurd . (Bool.not_eq_true _ ▸ hc))⟩

theorem BigStep.from_denote (h: (s, s'') ∈ ⟦c⟧): (c, s) ==> s'' := by
  induction c generalizing s s'' with
  | skip => exact SRel.mem_id.mp h ▸ skip
  | ass => exact h ▸ ass
  | cat _ _ ihcatl ihcatr =>
    exact match h with | ⟨s', hl, hr⟩ => cat s' (ihcatl hl) (ihcatr hr)
  | ifElse _ _ _ ih1 ih2 =>
    exact match h with
    | .inl ⟨hs, hc⟩ => ifTrue hc (ih1 hs)
    | .inr ⟨hs, hc⟩ => ifFalse (Bool.not_eq_true _ ▸ hc) (ih2 hs)
  | whileLoop b c ih =>
    have hle: ⟦whileLoop b c⟧ ≤ {(s, s'') | (whileLoop b c, s) ==> s''} :=
      OrderHom.lfp_le fun (_, _) hmp =>
        match hmp with
        | .inl ⟨⟨s', hs, hrest⟩, hc⟩ =>
          whileTrue s' hc (ih hs) hrest
        | .inr ⟨hid, hc⟩ =>
          (SRel.mem_id.mp hid) ▸ whileFalse (Bool.not_eq_true _ ▸ hc)

    exact hle h

theorem natural_eq_denote: (s, s') ∈ ⟦c⟧ ↔ (c, s) ==> s' :=
  ⟨BigStep.from_denote, denote.from_natural⟩

theorem structural_eq_denote: (c, s) ~>* (∅, s') ↔ (s, s') ∈ ⟦c⟧ :=
  by rw [structural_eq_natural, natural_eq_denote]

end Com
