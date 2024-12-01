/-
# Maps
-/

/-
## Total maps
-/

def Map A := String → A

def TotalMap.default (v: A): Map A := λ _ => v

def TotalMap.update (m: Map A) (k: String) (v: A) :=
  λ k' => bif k == k' then v else m k'

notation m "[" k " ← " v "]" => TotalMap.update m k v

namespace TotalMap

theorem eval:
  (m[k ← v]) k = v := by
  unfold TotalMap.update
  rw [beq_self_eq_true, cond_true]

theorem eval_neq (hneq: k != k'):
  (m[k ← v]) k' = m k' := by
  unfold TotalMap.update
  rw [bne_iff_ne] at hneq
  rw [Bool.cond_neg]
  rw [beq_eq_false_iff_ne, ne_eq]
  exact hneq

theorem eval_last:
  m[k ← v₂][k ← v₁] = m[k ← v₁] := by
  funext k'
  match h: k == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true, cond_true]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false, cond_false, cond_false]

theorem eval_swap (hneq : k₁ != k₂):
  m[k₂ ← v₂][k₁ ← v₁] = m[k₁ ← v₁][k₂ ← v₂] := by
  funext k'
  match h: k₁ == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true]
    match h': k₂ == k' with
    | true =>
      rw [eq_of_beq h, eq_of_beq h', bne_iff_ne] at hneq
      contradiction
    | false =>
      rw [cond_false, cond_true]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false, cond_false]

theorem eval_id:
  m[k ← m k] = m := by
  funext k'
  match h: k == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true, eq_of_beq h]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false]

theorem eval_same:
  (λ _ => v)[k ← v] = λ _ => v := by
  funext k'
  match h: k == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false]

example (m: Map Nat):
  m["a" ← 0]["a" ← 2] = m["a" ← 2] := eval_last

example (m: Map Nat):
  m["a" ← 0]["b" ← 2] = m["b" ← 2]["a" ← 0] := by
  apply eval_swap
  simp only [String.reduceBNe]

example (m: Map Nat):
  m["a" ← m "a"]["b" ← 0] = m["b" ← 0] := eval_id ▸ rfl

end TotalMap

/-
## Partial maps
-/

def PartialMap A := Map (Option A)

def PartialMap.default: PartialMap A := TotalMap.default none
