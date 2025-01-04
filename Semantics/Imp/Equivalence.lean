import Semantics.Imp.BigStep
import Semantics.Imp.SmallStep
import Semantics.Imp.Denotational

namespace Com

theorem SmallStep.from_natural {x: Com × State}
  (hx: x ==> s'): x ~>* (∅, s') := by
  induction hx with
  | skip => exact .refl
  | ass => exact .single ass
  | cat _ _ _ ihcatl ihcatr => exact star.cat ihcatl ihcatr
  | ifTrue hcond _ ih => exact .head ifElse (hcond ▸ ih)
  | ifFalse hcond _ ih => exact .head ifElse (hcond ▸ ih)
  | whileTrue _ hcond _ _ ihc ihw =>
    exact .head whileLoop (.trans (hcond ▸ star.cat ihc ihw) .refl)
  | whileFalse hcond =>
    exact .head whileLoop (hcond ▸ .refl)

theorem BigStep.from_structural_step
  (hx: x ~> x') (hx': x' ==> s'): x ==> s' := by
  induction hx generalizing s' with
  | ass => exact (skip_eq.mp hx') ▸ ass
  | skipCat => exact cat _ skip hx'
  | cat _ ih => match hx' with
    | cat s' hcatl hccatr => exact cat s' (ih hcatl) hccatr
  | ifElse => rw [if_eq']; exact hx'
  | whileLoop => rw [loop_unfold, if_eq']; exact hx'

theorem BigStep.from_structural
  (hx: x ~>* (∅, s')): x ==> s' := by
  induction hx using ReflTrans.head_induction_on with
  | refl => exact skip
  | head hsingle _ hs' => exact from_structural_step hsingle hs'

theorem structural_eq_natural:
  ((c, s) ~>* (∅, s')) ↔ ((c, s) ==> s') :=
  ⟨BigStep.from_structural, SmallStep.from_natural⟩

theorem denote.from_natural {x: Com × State}
  (hx: x ==> s''): (x.2, s'') ∈ ⟦x.1⟧ := by
  induction hx with
  | skip => exact rfl
  | ass  => exact rfl
  | cat s' _ _ ihcatl ihcatr => exact ⟨s', ihcatl, ihcatr⟩
  | ifTrue hcond _ ih => exact .inl ⟨ih, hcond⟩
  | ifFalse hcond _ ih =>
    exact .inr ⟨ih, (absurd . (Bool.not_eq_true _ ▸ hcond))⟩
  | whileTrue s' hcond _ _ ihwhilestep ihwhilerest =>
    exact Denotational.while_unfold ▸
      .inl ⟨⟨s', ihwhilestep, ihwhilerest⟩, hcond⟩
  | whileFalse hcond =>
    exact Denotational.while_unfold ▸
      .inr ⟨denote.eq_1 ▸ rfl, (absurd . (Bool.not_eq_true _ ▸ hcond))⟩

theorem BigStep.from_denote (hmem: (s, s'') ∈ ⟦c⟧): (c, s) ==> s'' := by
  revert hmem
  induction c generalizing s s'' with
  | skip => exact (SRel.mem_id.mp . ▸ skip)
  | ass => exact (. ▸ ass)
  | cat _ _ ihcatl ihcatr =>
    exact fun ⟨s', hl, hr⟩ => cat s' (ihcatl hl) (ihcatr hr)
  | ifElse _ _ _ ih1 ih2 =>
    intro hmp
    match hmp with
    | .inl ⟨hstep, hcond⟩ => exact ifTrue hcond (ih1 hstep)
    | .inr ⟨hstep, hcond⟩ =>
      exact ifFalse (Bool.not_eq_true _ ▸ hcond) (ih2 hstep)
  | whileLoop b c ih =>
    have h: ⟦whileLoop b c⟧ ≤ {(s, s'') | (whileLoop b c, s) ==> s''} :=
      OrderHom.lfp_le fun (_, _) hmp =>
        match hmp with
        | .inl ⟨⟨s', hstep, hrest⟩, hcond⟩ =>
          whileTrue s' hcond (ih hstep) hrest
        | .inr ⟨hid, hcond⟩ =>
          (SRel.mem_id.mp hid) ▸ whileFalse (Bool.not_eq_true _ ▸ hcond)

    apply h

theorem natural_eq_denote: ((s, s') ∈ ⟦c⟧) ↔ ((c, s) ==> s') :=
  ⟨BigStep.from_denote, denote.from_natural⟩

theorem structural_eq_denote: ((c, s) ~>* (∅, s')) = ((s, s') ∈ ⟦c⟧) :=
  by rw [structural_eq_natural, natural_eq_denote]

end Com
