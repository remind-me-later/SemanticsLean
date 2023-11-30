import Semantics.Stlc.Syntax

namespace Term
namespace Natural

inductive Value: Term → Prop where
  | abs₁: Value (abs _ _ _)
  | true₁: Value true
  | false₁: Value false

def subst (x: String) (s: Term) (t: Term): Term :=
  match t with
  | var y => bif x = y then s else t
  | abs y T t₁ => bif x = y then t else abs y T (subst x s t₁)
  | app t₁ t₂ => app (subst x s t₁) (subst x s t₂)
  | cond t₁ t₂ t₃ => cond (subst x s t₁) (subst x s t₂) (subst x s t₃)
  | otherwise => otherwise

end Natural
end Term
