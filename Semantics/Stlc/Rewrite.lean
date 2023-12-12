import Semantics.Stlc.Lang
import Mathlib.Logic.Relation

def value: Term → Bool
  | Term.abs _ _ _ | Term.tt | Term.ff => true
  | _ => false

def subst (x: String) (s: Term) (t: Term): Term :=
  match t with
  | Term.var y => bif x = y then s else t
  | Term.abs y T t₁ => bif x = y then t else Term.abs y T (subst x s t₁)
  | Term.app t₁ t₂ => Term.app (subst x s t₁) (subst x s t₂)
  | Term.cond t₁ t₂ t₃ => Term.cond (subst x s t₁) (subst x s t₂) (subst x s t₃)
  | otherwise => otherwise

notation "[" x "≔" s "]" t => subst x s t

inductive step: Term → Term → Prop where
  | appabs (h: value v):
    step (Term.app (Term.abs x _ t) v) ([x ≔ v]t)

  | app₁ (h₁: step t t'):
    step (Term.app t u) (Term.app t' u)

  | app₂ (h₁: value v) (h₂: step u u'):
    step (Term.app v u) (Term.app v u')

  | cond₁:
    step (Term.cond tt t _) t

  | cond₂:
    step (Term.cond ff _ u) u

  | cond₃ (h: step b b'):
    step (Term.cond b t u) (Term.cond b' t u)

infix:100 " ⇒ " => step

infix:110 " ⇒* " => Relation.ReflTransGen step
