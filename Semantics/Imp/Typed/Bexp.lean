import Semantics.Imp.Typed.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
inductive Step: Bexp → State → Bool → Prop
  | tt: Step tt _ true
  | ff: Step ff _ false
  | leₙ
    (h₁: Aexp.Natural.Step a s (Val.nat n))
    (h₂: Aexp.Natural.Step b s (Val.nat m)):
    Step (le a b) s (n ≤ m)
  | leᵢ
    (h₁: Aexp.Natural.Step a s (Val.int n))
    (h₂: Aexp.Natural.Step b s (Val.int m)):
    Step (le a b) s (n ≤ m)
  | not
    (h: Step a s n):
    Step (not a) s (!n)
  | and
    (h₁: Step a s n) (h₂: Step b s m):
    Step (and a b) s (n && m)

end Natural
end Bexp
