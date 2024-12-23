-- Reflexive transitive relations
inductive ReflTrans (r: α → α → Prop): α → α → Prop
  | refl: ReflTrans r a a
  | tail: ReflTrans r a b → r b c → ReflTrans r a c

namespace ReflTrans

theorem trans (hab: ReflTrans r a b) (hbc: ReflTrans r b c): ReflTrans r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hcd hac => exact tail hac hcd

theorem single (hab: r a b): ReflTrans r a b :=
  tail refl hab

theorem head (hab: r a b) (hbc: ReflTrans r b c): ReflTrans r a c := by
  induction hbc with
  | refl => exact tail refl hab
  | tail _ hcd hac => exact tail hac hcd

theorem head_induction_on {P: ∀a: α, ReflTrans r a b → Prop} {a: α} (h: ReflTrans r a b)
    (refl: P b refl)
    (head: ∀{a c} (h': r a c) (h: ReflTrans r c b), P c h → P a (head h' h)): P a h := by
  induction h with
  | refl => exact refl
  | tail _ hbc ih =>
    exact ih (head hbc _ refl) (fun h1 h2 => head h1 (tail h2 hbc))

theorem lift {r: α → α → Prop} {p: β → β → Prop} {a b: α} (f: α → β)
    (h: ∀{a b}, r a b → p (f a) (f b)) (hab: ReflTrans r a b): ReflTrans p (f a) (f b) := by
  induction hab with
  | refl => exact refl
  | tail _hab hbc ih => exact tail ih (h hbc)

end ReflTrans
