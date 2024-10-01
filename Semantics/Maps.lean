/-
# Maps
-/

/-
## Total maps
-/

def TotalMap A := String → A

def TotalMap.default (v: A): TotalMap A := fun _ => v

def TotalMap.update (m: TotalMap A) (k: String) (v: A) :=
  fun k' => if k = k' then v else m k'

notation m "⟪" k " ≔ " v "⟫" => TotalMap.update m k v

namespace TotalMap

theorem ev: (m⟪k ≔ v⟫) k = v := if_pos rfl

theorem ev_neq (hneq: k ≠ k'):
    (m⟪k ≔ v⟫) k' = m k' := if_neg hneq

theorem clobber: m⟪k ≔ v₂⟫⟪k ≔ v₁⟫ = m⟪k ≔ v₁⟫ :=
  funext fun k' => by
    cases Classical.em (k = k') with
    | inl h => exact h ▸ ev ▸ ev ▸ rfl
    | inr h => exact ev_neq h ▸ ev_neq h ▸ ev_neq h ▸ rfl

theorem ev_swap (hneq : k₁ ≠ k₂):
  m⟪k₂ ≔ v₂⟫⟪k₁ ≔ v₁⟫ = m⟪k₁ ≔ v₁⟫⟪k₂ ≔ v₂⟫ :=
  funext fun k' => by
    cases Classical.em (k₁ = k') with
    | inl h => rw [h, ev,
                    ev_neq (h ▸ hneq).symm, ev]
    | inr h =>
      cases Classical.em (k₂ = k') with
      | inl h' => rw [h', ev, ev_neq h, ev]
      | inr h' => rw [ev_neq h, ev_neq h',
                      ev_neq h', ev_neq h]

theorem ev_id: m⟪k ≔ m k⟫ = m :=
  funext fun k' => by
    cases Classical.em (k = k') with
    | inl h => exact h ▸ ev
    | inr h => exact ev_neq h

theorem ev_same: (fun _ => v)⟪k ≔ v⟫ = (fun _ => v) :=
  funext fun k' => by
    cases Classical.em (k = k') with
    | inl h => exact h ▸ ev
    | inr h => exact ev_neq h

example (m: TotalMap Nat):
  m⟪"a" ≔ 0⟫⟪"a" ≔ 2⟫ = m⟪"a" ≔ 2⟫ := clobber

example (m: TotalMap Nat):
  m⟪"a" ≔ 0⟫⟪"b" ≔ 2⟫ = m⟪"b" ≔ 2⟫⟪"a" ≔ 0⟫ :=
  ev_swap (fun h => by contradiction)

example (m: TotalMap Nat):
  m⟪"a" ≔ m "a"⟫⟪"b" ≔ 0⟫ = m⟪"b" ≔ 0⟫ := ev_id ▸ rfl

end TotalMap

/-
## Partial maps
-/

def PartialMap A := TotalMap (Option A)

def PartialMap.default: PartialMap A := TotalMap.default none
