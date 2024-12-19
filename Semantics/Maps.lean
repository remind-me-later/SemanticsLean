/-
# Maps
-/

/-
## Total maps
-/

def Map (α: Type) := String -> α

namespace Map

def default (v: α): Map α := fun _ => v

def update (k: String) (v: α) (m: Map α) :=
  fun k' => bif k == k' then v else m k'

notation m "[" k " <- " v "]" => Map.update k v m

theorem eval:
  (m[k <- v]) k = v := by
  unfold Map.update
  rw [beq_self_eq_true, cond_true]

theorem neval (hneq: k != k'):
  (m[k <- v]) k' = m k' := by
  unfold Map.update
  rw [bne_iff_ne] at hneq
  rw [Bool.cond_neg]
  rw [beq_eq_false_iff_ne, ne_eq]
  exact hneq

theorem forget:
  m[k <- v'][k <- v] = m[k <- v] := by
  funext k'
  match h: k == k' with
  | true =>
    unfold Map.update
    rw [h, cond_true, cond_true]
  | false =>
    unfold Map.update
    rw [h, cond_false, cond_false, cond_false]

theorem comm (hneq: k != k'):
  m[k' <- v'][k <- v] = m[k <- v][k' <- v'] := by
  funext k''
  match h: k == k'' with
  | true =>
    unfold Map.update
    rw [h, cond_true]
    match h': k' == k'' with
    | true =>
      rw [eq_of_beq h, eq_of_beq h', bne_iff_ne] at hneq
      contradiction
    | false =>
      rw [cond_false, cond_true]
  | false =>
    unfold Map.update
    rw [h, cond_false, cond_false]

theorem idem:
  m[k <- m k] = m := by
  funext k'
  match h: k == k' with
  | true =>
    unfold Map.update
    rw [h, cond_true, eq_of_beq h]
  | false =>
    unfold Map.update
    rw [h, cond_false]

theorem eval_same:
  (fun _ => v)[k <- v] = fun _ => v := by
  funext k'
  match h: k == k' with
  | true =>
    unfold Map.update
    rw [h, cond_true]
  | false =>
    unfold Map.update
    rw [h, cond_false]

example (m: Map Nat):
  m["a" <- 0]["a" <- 2] = m["a" <- 2] := forget

example (m: Map Nat):
  m["a" <- 0]["b" <- 2] = m["b" <- 2]["a" <- 0] := by
  apply comm
  simp only [String.reduceBNe]

example (m: Map Nat):
  m["a" <- m "a"]["b" <- 0] = m["b" <- 0] := idem ▸ rfl

end Map

/-
## Partial maps
-/

def PMap (α: Type) := Map (Option α)

namespace PMap

def default: PMap α := Map.default none

end PMap
