/-
# Maps
-/

/-
## Total maps
-/

def TotalMap A := String → A

def TotalMap.default (v: A): TotalMap A := λ _ ↦ v

def TotalMap.update (m: TotalMap A) (k: String) (v: A) :=
  λ k' ↦ if k = k' then v else m k'

notation m "⟪" k " ≔ " v "⟫" => TotalMap.update m k v

theorem update_apply: (m⟪k ≔ v⟫) k = v := if_pos rfl

theorem update_apply_neq (hneq: k ≠ k'):
    (m⟪k ≔ v⟫) k' = m k' := if_neg hneq

theorem update_override: m⟪k ≔ v₂⟫⟪k ≔ v₁⟫ = m⟪k ≔ v₁⟫ :=
  by
    apply funext
    intro k'
    cases Classical.em (k = k') with
    | inl h => rw [h, update_apply, update_apply]
    | inr h => rw [update_apply_neq h, update_apply_neq h, update_apply_neq h]

theorem update_swap (hneq : k₁ ≠ k₂):
  m⟪k₂ ≔ v₂⟫⟪k₁ ≔ v₁⟫ = m⟪k₁ ≔ v₁⟫⟪k₂ ≔ v₂⟫ :=
  by
    apply funext
    intro k'
    cases Classical.em (k₁ = k') with
    | inl h => rw [h, update_apply,
                    update_apply_neq (h ▸ hneq).symm, update_apply]
    | inr h =>
      cases Classical.em (k₂ = k') with
      | inl h' => rw [h', update_apply, update_apply_neq h, update_apply]
      | inr h' => rw [update_apply_neq h, update_apply_neq h',
                      update_apply_neq h', update_apply_neq h]

theorem update_id: m⟪k ≔ m k⟫ = m :=
  by
    apply funext
    intro k'
    cases Classical.em (k = k') with
    | inl h => rw [h, update_apply]
    | inr h => rw [update_apply_neq h]

theorem update_same_const: (λ _ ↦ v)⟪k ≔ v⟫ = (λ _ ↦ v) :=
  by
    apply funext
    intro k'
    cases Classical.em (k = k') with
    | inl h => rw [h, update_apply]
    | inr h => rw [update_apply_neq h]

example (m: TotalMap Nat):
  m⟪"a" ≔ 0⟫⟪"a" ≔ 2⟫ = m⟪"a" ≔ 2⟫ := update_override

example (m: TotalMap Nat):
  m⟪"a" ≔ 0⟫⟪"b" ≔ 2⟫ = m⟪"b" ≔ 2⟫⟪"a" ≔ 0⟫ :=
  by
    apply update_swap
    intro h
    contradiction

example (m: TotalMap Nat):
  m⟪"a" ≔ m "a"⟫⟪"b" ≔ 0⟫ = m⟪"b" ≔ 0⟫ :=
  by
    rw [update_id]

/-
## Partial maps
-/

def PartialMap A := TotalMap (Option A)

def PartialMap.default: PartialMap A := TotalMap.default none
