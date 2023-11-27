import Imp.Natural
import Imp.Structural
import Imp.Denot

theorem Com.Nat_imp_Star {cs: Com × State} (h: cs ⟹ t): cs ⇒* (skip, t) := by
  induction h with
  | skip₁ => exact Relation.ReflTransGen.refl
  | ass₁ => exact Relation.ReflTransGen.single Step.ass₁
  | cat₁ _ _ _ ihc ihd => exact Star.cat ihc ihd
  | ife₁ hb _ ih =>
    exact Relation.ReflTransGen.head Step.ife₁ (hb ▸ ih)
  | ife₂ hb _ ih =>
    exact Relation.ReflTransGen.head Step.ife₁ (hb ▸ ih)
  | wle₁ _ hb _ _ ihc ihw =>
    apply Relation.ReflTransGen.head Step.wle₁
    exact Relation.ReflTransGen.head Step.ife₁ (hb ▸ Star.cat ihc ihw)
  | wle₂ hb =>
    apply Relation.ReflTransGen.head Step.wle₁
    apply Relation.ReflTransGen.head _ Relation.ReflTransGen.refl
    exact (Step.ite_false hb).mpr rfl

lemma Com.Step_imp_Nat (h₁: cs₀ ⇒ cs₁) (h₂: cs₁ ⟹ s₂): cs₀ ⟹ s₂ := by
  induction h₁ generalizing s₂ with
  | ass₁ => cases h₂; exact Nat.ass₁
  | cat₁ => exact Nat.cat₁ _ Nat.skip₁ h₂
  | cat₂ _ ih =>
    cases h₂ with
    | cat₁ _ hc hd => exact Nat.cat₁ _ (ih hc) hd
  | ife₁ => exact Nat.ife_ext''.mpr h₂
  | wle₁ => rw [Nat.wle_unfold]; exact h₂

theorem Com.Star_imp_Nat (h: cs ⇒* (skip, t)): cs ⟹ t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Nat.skip₁
  | head cs cs' ht => cases cs' <;> exact Step_imp_Nat cs ht

theorem Com.Star_iff_Nat: cs ⇒* (skip, t) ↔ cs ⟹ t := ⟨Star_imp_Nat, Nat_imp_Star⟩

theorem Com.denot.of_Nat {cs: Com × State} (h : cs ⟹ t):
  (cs.2, t) ∈ ⟦cs.1⟧ := by
  induction h with
  | skip₁ => simp [denot]
  | ass₁  => simp [denot]
  | cat₁ t _ _ ih₁ ih₂ =>
    simp at *
    exists t
  | ife₁ hb _ ih =>
    simp at *
    simp [denot, Or.inl, SRel.restrict, hb, ih]
  | ife₂ hb _ ih =>
    simp at *
    simp [denot, Or.inr, SRel.restrict, hb, ih]
  | wle₁ t hb _ _ ih₁ ih₂ =>
    simp at *
    rw [wle_unfold]
    simp [denot]
    apply Or.inl
    apply And.intro _ hb
    exists t
  | wle₂ hb =>
    simp at *
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
  | ife _ _ _ ih₁ ih₂ =>
    intro h
    cases h with
    | inl h =>
      simp at *
      cases h with | intro h hb =>
        exact ife₁ hb (ih₁ h)
    | inr h =>
      simp at *
      cases h with | intro h hb =>
        exact ife₂ hb (ih₂ h)
  | wle b c ih =>
    suffices ⟦wle b c⟧ ≤ {st | (wle b c, st.1) ⟹ st.2} by apply this
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
