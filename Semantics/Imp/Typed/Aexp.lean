import Semantics.Imp.Typed.Lang

namespace Aexp
namespace Natural

-- Operational semantics of aexp
inductive Step: Aexp → State → Val → Prop
  | val: Step (val n) _ n
  | var: Step (var x) s v
  | addₙ
    (h₁: Step a s $ Val.nat n) (h₂: Step b s $ Val.nat m):
    Step (add a b) s (Val.nat $ n + m)
  | addᵢ
    (h₁: Step a s (Val.int n)) (h₂: Step b s (Val.int m)):
    Step (add a b) s (Val.int $ n + m)

end Natural
end Aexp
