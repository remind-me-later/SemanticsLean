import Semantics.Stlc.Lang
import Mathlib.Logic.Relation

def value: Term → Bool
  | Λ _:_↦_ | ⊤ | ⊥ => true
  | _ => false

def subst (x: String) (s: Term) (t: Term): Term :=
  match t with
  | Term.var y => bif x = y then s else t
  | Λ y:T↦t₁ => bif x = y then t else Λ y:T↦(subst x s t₁)
  | t₁..t₂ => (subst x s t₁)..(subst x s t₂)
  | t₁ ? t₂ | t₃ => (subst x s t₁) ? subst x s t₂ | subst x s t₃
  | otherwise => otherwise

notation "[" x "≔" s "]" t => subst x s t

inductive step: Term → Term → Prop where
  | appabs (h: value v):
    step ((Λ x:_ ↦ t)..v) ([x ≔ v]t)

  | app₁ (h₁: step t t'):
    step (t..u) (t'..u)

  | app₂ (h₁: value v) (h₂: step u u'):
    step (v..u) (v..u')

  | cond₁:
    step (⊤ ? t | _) t

  | cond₂:
    step (⊥ ? _ | u) u

  | cond₃ (h: step b b'):
    step (b ? t | u) (b' ? t | u)

infix:100 " ⇒ " => step

infix:110 " ⇒* " => Relation.ReflTransGen step
