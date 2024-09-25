/-
# Maps
-/

/-
## Total maps
-/

def TotalMap A := String → A

def TotalMap.default (v: A): TotalMap A := λ _ ↦ v

def TotalMap.update (map: TotalMap A) (key: String) (val: A) :=
  λ key' ↦ if key = key' then val else map key'

notation map "⟪" key " ≔ " val "⟫" => TotalMap.update map key val

@[simp] theorem update_apply (key : String) (val : A) (map : TotalMap A) :
  (map⟪key ≔ val⟫) key = val :=
  by
    apply if_pos
    rfl

@[simp] theorem update_apply_neq (key key' : String) (val : A) (map : TotalMap A)
    (hneq : key ≠ key'):
    (map⟪key ≔ val⟫) key' = map key' :=
    by
      apply if_neg
      assumption

@[simp] theorem update_override (name : String) (val₁ val₂ : A) (s : TotalMap A) :
  s⟪name ≔ val₂⟫⟪name ≔ val₁⟫ = s⟪name ≔ val₁⟫ :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h =>
      cases h
      rw [update_apply, update_apply]
    | inr h =>
      rw [update_apply_neq]
      . rw [update_apply_neq]
        . rw [update_apply_neq]
          rw [ne_comm, ne_eq]
          exact h
        . rw [ne_comm, ne_eq]
          exact h
      . rw [ne_comm, ne_eq]
        exact h

@[simp] theorem update_swap (name₁ name₂ : String) (val₁ val₂ : A) (s : TotalMap A)
    (hneq : name₁ ≠ name₂) :
  s⟪name₂ ≔ val₂⟫⟪name₁ ≔ val₁⟫ = s⟪name₁ ≔ val₁⟫⟪name₂ ≔ val₂⟫ :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name₁) with
    | inl h =>
      cases h
      rw [update_apply, update_apply_neq]
      . rw [update_apply]
      . rw [ne_comm]
        exact hneq
    | inr h =>
      cases Classical.em (name' = name₁) with
      | inl h₁ =>
        cases h₁
        rw [eq_self] at h
        contradiction
      | inr h₁ =>
        cases Classical.em (name' = name₂) with
        | inl h₂ =>
          cases h₂
          rw [update_apply, update_apply_neq]
          . rw [update_apply]
          . rw [ne_comm, ne_eq]
            exact h
        | inr h₂ =>
          rw [update_apply_neq]
          . rw [update_apply_neq]
            . rw [update_apply_neq]
              . rw [update_apply_neq]
                rw [ne_comm, ne_eq]
                exact h
              . rw [ne_comm, ne_eq]
                exact h₂
            . rw [ne_comm, ne_eq]
              assumption
          . rw [ne_comm, ne_eq]
            exact h

@[simp] theorem update_id (name : String) (s : TotalMap A) :
  s⟪name ≔ s name⟫ = s :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h =>
      cases h
      rw [update_apply]
    | inr h =>
      rw [update_apply_neq]
      rw [ne_comm, ne_eq]
      exact h

@[simp] theorem update_same_const (name : String) (val : A) :
  (λ _ ↦ val)⟪name ≔ val⟫ = (λ _ ↦ val) :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h =>
      cases h
      rw [update_apply]
    | inr h =>
      rw [update_apply_neq]
      rw [ne_comm, ne_eq]
      exact h

example (map : TotalMap Nat) :
  map⟪"a" ≔ 0⟫⟪"a" ≔ 2⟫ = map⟪"a" ≔ 2⟫ :=
  by simp

example (map : TotalMap Nat) :
  map⟪"a" ≔ 0⟫⟪"b" ≔ 2⟫ = map⟪"b" ≔ 2⟫⟪"a" ≔ 0⟫ :=
  by simp

example (map : TotalMap Nat) :
  map⟪"a" ≔ map "a"⟫⟪"b" ≔ 0⟫ = map⟪"b" ≔ 0⟫ :=
  by simp

/-
## Partial maps
-/

def PartialMap A := TotalMap (Option A)

def PartialMap.default: PartialMap A := TotalMap.default none
