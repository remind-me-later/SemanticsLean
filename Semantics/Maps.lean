/-
# Maps
-/

/-
## Total maps
-/

def Map (α: Type) := String → α

namespace Map

def default (v: α): Map α := λ _ ↦ v

def update (m: Map α) (k: String) (v: α) :=
  λ k' ↦ bif k == k' then v else m k'

notation m "[" k " ← " v "]" => Map.update m k v

theorem eval:
  (m[k ← v]) k = v := by
  unfold Map.update
  rw [beq_self_eq_true, cond_true]

theorem eval_neq (hneq: k != k'):
  (m[k ← v]) k' = m k' := by
  unfold Map.update
  rw [bne_iff_ne] at hneq
  rw [Bool.cond_neg]
  rw [beq_eq_false_iff_ne, ne_eq]
  exact hneq

theorem eval_last:
  m[k ← v₂][k ← v₁] = m[k ← v₁] := by
  funext k'
  match h: k == k' with
  | true =>
    unfold Map.update
    rw [h, cond_true, cond_true]
  | false =>
    unfold Map.update
    rw [h, cond_false, cond_false, cond_false]

theorem eval_swap (hneq : k₁ != k₂):
  m[k₂ ← v₂][k₁ ← v₁] = m[k₁ ← v₁][k₂ ← v₂] := by
  funext k'
  match h: k₁ == k' with
  | true =>
    unfold Map.update
    rw [h, cond_true]
    match h': k₂ == k' with
    | true =>
      rw [eq_of_beq h, eq_of_beq h', bne_iff_ne] at hneq
      contradiction
    | false =>
      rw [cond_false, cond_true]
  | false =>
    unfold Map.update
    rw [h, cond_false, cond_false]

theorem eval_id:
  m[k ← m k] = m := by
  funext k'
  match h: k == k' with
  | true =>
    unfold Map.update
    rw [h, cond_true, eq_of_beq h]
  | false =>
    unfold Map.update
    rw [h, cond_false]

theorem eval_same:
  (λ _ ↦ v)[k ← v] = λ _ ↦ v := by
  funext k'
  match h: k == k' with
  | true =>
    unfold Map.update
    rw [h, cond_true]
  | false =>
    unfold Map.update
    rw [h, cond_false]

example (m: Map Nat):
  m["a" ← 0]["a" ← 2] = m["a" ← 2] := eval_last

example (m: Map Nat):
  m["a" ← 0]["b" ← 2] = m["b" ← 2]["a" ← 0] := by
  apply eval_swap
  simp only [String.reduceBNe]

example (m: Map Nat):
  m["a" ← m "a"]["b" ← 0] = m["b" ← 0] := eval_id ▸ rfl

end Map

/-
## Partial maps
-/

def PMap (α: Type) := Map (Option α)

namespace PMap

def default: PMap α := Map.default none

end PMap
