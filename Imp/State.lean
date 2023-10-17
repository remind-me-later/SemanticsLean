def State := String → Int
notation "Σ" => State

def empty_state: Σ := fun _ => 0

def update (σ: Σ) (x: String) (n: Int): Σ := 
  fun x' => if x' = x then n else σ x'

notation "⟦""⟧" => empty_state
notation s "⟦" x "↦" n "⟧" => update s x n
notation "⟦" x "↦" n "⟧" => update ⟦⟧ x n
