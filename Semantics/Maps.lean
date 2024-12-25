/-
# Maps
-/

/-
## Total maps
-/

def Map (α: Type) := String → α

namespace Map

def default (v: α): Map α := fun _ => v

def update (k: String) (v: α) (m: Map α): Map α
  | k' => match k == k' with | true => v | false => m k'

notation m "[" k " ← " v "]" => Map.update k v m

theorem eval:
  (m[k ← v]) k = v := by
  simp only [Map.update]
  exact beq_self_eq_true k ▸ rfl

theorem neval (hneq: k != k'):
  (m[k ← v]) k' = m k' := by
  unfold Map.update
  exact Bool.cond_neg (beq_eq_false_iff_ne.mpr $ bne_iff_ne.mp hneq)

theorem forget:
  m[k ← v'][k ← v] = m[k ← v] := by
  funext k'
  simp only [Map.update]
  match k == k' with | true | false => rfl

theorem comm (hneq: k != k'):
  m[k' ← v'][k ← v] = m[k ← v][k' ← v'] := by
  funext k''
  simp only [Map.update]
  match h: k == k'' with
  | true =>
    match h': k' == k'' with
    | true =>
      rw [bne_iff_ne, eq_of_beq h, eq_of_beq h'] at hneq
      apply absurd rfl hneq
    | false => rfl
  | false => rfl

theorem idem:
  m[k ← m k] = m := by
  funext k'
  simp only [Map.update]
  match h: k == k' with
  | true => rw [eq_of_beq h]
  | false => rfl

theorem eval_same:
  (fun _ => v)[k ← v] = fun _ => v := by
  funext k'
  simp only [Map.update]
  match h: k == k' with
  | true => rfl
  | false => rfl

example (m: Map Nat):
  m["a" ← 0]["a" ← 2] = m["a" ← 2] := forget

example (m: Map Nat):
  m["a" ← 0]["b" ← 2] = m["b" ← 2]["a" ← 0] := by
  apply comm
  simp only [String.reduceBNe]

example (m: Map Nat):
  m["a" ← m "a"]["b" ← 0] = m["b" ← 0] := idem ▸ rfl

end Map

/-
## Partial maps
-/

def PMap (α: Type) := Map (Option α)

namespace PMap

def default: PMap α := Map.default none

end PMap
