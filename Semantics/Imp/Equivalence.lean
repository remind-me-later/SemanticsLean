import Semantics.Imp.Natural
import Semantics.Imp.Structural
import Semantics.Imp.Denotational

namespace Com

theorem Structural.from_natural {conf: Com × State}
  (hconf: conf ==> s'): conf ~>* (skip, s') := by
  induction hconf with
  | skip => exact RTL.refl
  | ass => exact RTL.single small_step.ass
  | cat _ _ _ ihcatl ihcatr => exact star.cat ihcatl ihcatr
  | iftrue hcond _ ih => exact RTL.head small_step.ifelse (hcond ▸ ih)
  | iffalse hcond _ ih => exact RTL.head small_step.ifelse (hcond ▸ ih)
  | whiletrue _ hcond _ _ ihc ihw =>
    exact RTL.head small_step.whileloop (RTL.trans (hcond ▸ star.cat ihc ihw) RTL.refl)
  | whilefalse hcond =>
    exact RTL.head small_step.whileloop (hcond ▸ RTL.refl)

theorem Natural.from_structural_step
  (hconf: conf ~> conf') (hconf': conf' ==> s'): conf ==> s' := by
  induction hconf generalizing s' with
  | ass => exact (skip_eq.mp hconf') ▸ big_step.ass
  | skipcat => exact big_step.cat _ big_step.skip hconf'
  | cat _ ih =>
    match hconf' with
    | big_step.cat s' hcatl hccatr => exact big_step.cat s' (ih hcatl) hccatr
  | ifelse => exact if_eq' ▸ hconf'
  | whileloop => rw [loop_unfold]; exact if_eq' ▸ hconf'

theorem Natural.from_structural
  (hconf: conf ~>* (skip, s')): conf ==> s' := by
  induction hconf using RTL.head_induction_on with
  | refl => exact big_step.skip
  | head hsingle _ hs' => exact from_structural_step hsingle hs'

theorem structural_eq_natural:
  ((c, s) ~>* (skip, s')) = ((c, s) ==> s') :=
  propext (Iff.intro Natural.from_structural Structural.from_natural)

theorem denote.from_natural {conf: Com × State}
  (hconf: conf ==> s''): (conf.2, s'') ∈ [[conf.1]] := by
  induction hconf with
  | skip => exact SFun.mem_id.mpr rfl
  | ass  => exact SFun.mem_id.mpr rfl
  | cat s' _ _ ihcatl ihcatr =>
    exact Exists.intro s' (And.intro ihcatl ihcatr)
  | iftrue hcond _ ih => exact Or.inl (And.intro ih hcond)
  | iffalse hcond _ ih =>
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hcond,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      exact ih
  | whiletrue s' hcond _ _ ihwhilestep ihwhilerest =>
    exact while_unfold ▸
      (Or.inl (And.intro
        (Exists.intro s' (And.intro ihwhilestep ihwhilerest)) hcond))
  | whilefalse hcond =>
      rw [while_unfold]
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hcond,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      rfl

theorem Natural.from_denote
  (hmem: (s, s'') ∈ [[c]]): (c, s) ==> s'' := by
  revert hmem
  induction c generalizing s s'' with
  | skip =>
    intro hmp
    rw [denote, SFun.mem_id] at hmp
    exact hmp ▸ big_step.skip
  | ass =>
    intro hmp
    rw [denote.eq_def, Set.mem_comprehend] at hmp
    simp only at hmp
    exact hmp ▸ big_step.ass
  | cat _ _ ihcatl ihcatr =>
    intro (Exists.intro s' (And.intro hl hr))
    exact big_step.cat s' (ihcatl hl) (ihcatr hr)
  | ifelse _ _ _ ih1 ih2 =>
    intro hmp
    match hmp with
    | Or.inl (And.intro hstep hcond) =>
      exact big_step.iftrue hcond (ih1 hstep)
    | Or.inr (And.intro hstep hcond) =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hcond
      exact big_step.iffalse hcond (ih2 hstep)
  | whileloop b c ih =>
    suffices
      [[while b loop c end]] ⊆ {(s, s'') | (while b loop c end, s) ==> s''} by
      apply this

    apply Fix.lfp_le
    intro (_, _) hmp
    match hmp with
    | Or.inl (And.intro (Exists.intro s' (And.intro hstep hrest)) hcond) =>
      exact big_step.whiletrue s' hcond (ih hstep) hrest
    | Or.inr (And.intro hid hcond) =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hcond
      rw [SFun.mem_id] at hid
      exact hid ▸ big_step.whilefalse hcond

theorem natural_eq_denote: ((s, s') ∈ [[c]]) = ((c, s) ==> s') :=
  propext (Iff.intro Natural.from_denote denote.from_natural)

theorem structural_eq_denote:
  ((c, s) ~>* (skip, s')) = ((s, s') ∈ [[c]]) :=
  by rw [structural_eq_natural, natural_eq_denote]

end Com
