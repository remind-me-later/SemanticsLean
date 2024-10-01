-- Reflexive transitive relations
inductive RTL (r : α → α → Prop) (a : α) : α → Prop
  | refl : RTL r a a
  | tail {b c} : RTL r a b → r b c → RTL r a c

namespace RTL

theorem trans (hab : RTL r a b) (hbc : RTL r b c) : RTL r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hcd hac => exact hac.tail hcd

theorem single (hab : r a b) : RTL r a b :=
  refl.tail hab

theorem head (hab : r a b) (hbc : RTL r b c) : RTL r a c := by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd

theorem head_induction_on {P : ∀ a : α, RTL r a b → Prop} {a : α} (h : RTL r a b)
    (refl : P b refl)
    (head : ∀ {a c} (h' : r a c) (h : RTL r c b), P c h → P a (h.head h')) : P a h := by
  induction h with
  | refl => exact refl
  | tail _ hbc ih =>
    apply ih
    · exact head hbc _ refl
    · exact fun h1 h2 => head h1 (h2.tail hbc)

theorem lift {r: α → α → Prop} {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → p (f a) (f b)) (hab : RTL r a b) : RTL p (f a) (f b) := by
  induction hab with
  | refl => exact refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

end RTL
