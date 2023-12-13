/-
# Maps
-/

/-
## Total maps
-/

def total_map A := String → A

def total_map.default (v: A): total_map A := λ _ ↦ v

def total_map.update (m: total_map A) (x: String) (v: A) :=
  λ y ↦ bif x = y then v else m y

notation m "⟪" x " ≔ " v "⟫" => total_map.update m x v

/-
## Partial maps
-/

def partial_map A := total_map $ Option A

def partial_map.default: partial_map A := λ _ ↦ none

def includedin (a b: partial_map A) := ∀ x v, (a x = some v) → (b x = some v)

theorem includedin_update x v (h: includedin a b):
  includedin (a ⟪x ≔ some v⟫) (b ⟪x ≔ some v⟫) :=  by
  {
    sorry
  }
