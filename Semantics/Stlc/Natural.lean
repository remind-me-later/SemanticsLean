import Semantics.Stlc.Syntax
import Mathlib.Logic.Relation

namespace Term
namespace Natural

inductive Value: Term → Prop where
  | abs: Value (abs _ _ _)
  | true: Value true
  | false: Value false

def subst (x: String) (s: Term) (t: Term): Term :=
  match t with
  | var y => bif x = y then s else t
  | abs y T t₁ => bif x = y then t else abs y T (subst x s t₁)
  | app t₁ t₂ => app (subst x s t₁) (subst x s t₂)
  | cond t₁ t₂ t₃ => cond (subst x s t₁) (subst x s t₂) (subst x s t₃)
  | otherwise => otherwise

notation "[" x "≔" s "]" t => subst x s t

inductive Step: Term → Term → Prop where
  | appabs (h: Value v):
    Step (app (abs x _ t) v) ([x ≔ v]t)

  | app₁ (h₁: Step t t'):
    Step (app t u) (app t' u)

  | app₂ (h₁: Value v) (h₂: Step u u'):
    Step (app v u) (app v u')

  | cond₁:
    Step (cond true t _) t

  | cond₂:
    Step (cond false _ u) u

  | cond₃ (h: Step b b'):
    Step (cond b t u) (cond b' t u)

infix:100 "⇒" => Step

infix:110 " ⇒* " => Relation.ReflTransGen Step




end Natural
end Term
