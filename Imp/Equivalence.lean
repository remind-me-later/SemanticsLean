import Imp.Natural
import Imp.Structural

theorem Com.Nat_imp_Star {cs: Com × State} (h: cs ⟹ t): cs ⇒* (skip, t) :=
  by
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

lemma Com.Step_imp_Nat (h₁: cs₀ ⇒ cs₁) (h₂: cs₁ ⟹ s₂): cs₀ ⟹ s₂ :=
  by
  induction h₁ generalizing s₂ with
  | ass₁ => cases h₂; exact Nat.ass₁
  | cat₁ => exact Nat.cat₁ _ Nat.skip₁ h₂
  | cat₂ _ ih =>
    cases h₂ with
    | cat₁ _ hc hd => exact Nat.cat₁ _ (ih hc) hd
  | ife₁ => exact Nat.ife_ext''.mpr h₂
  | wle₁ => rw [Nat.wle_unfold]; exact h₂

theorem Com.Star_imp_Nat (h: cs ⇒* (skip, t)): cs ⟹ t :=
  by induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Nat.skip₁
  | head cs cs' ht => cases cs' <;> exact Step_imp_Nat cs ht

theorem Com.Star_iff_Nat: cs ⇒* (skip, t) ↔ cs ⟹ t := ⟨Star_imp_Nat, Nat_imp_Star⟩
