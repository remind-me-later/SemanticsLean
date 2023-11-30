import Std.Logic
import Mathlib.Logic.Relation

/-
# Relations
-/

/-
## Abstract rewriting
-/

def normal_form (r: α → β → Prop) (t: α) :=
  ¬(∃ t₁, r t t₁)

theorem strong_progress {t: α} (r: α → β → Prop):
  (normal_form r t) ∨ (∃ t₁, r t t₁) :=
  by
  unfold normal_form
  apply Or.symm
  apply Classical.em

def normalizing (r: α → α → Prop) :=
  ∀t, ∃t₁, r t t₁ ∧ normal_form r t₁

def determinist (r: α → β → Prop) := ∀a b c, r a b → r a c → b = c

def reducing (r: α → β → Prop) :=
  ∀t, ∃t₁, r t t₁

/-
## Reflexive transitive closure
-/

alias Star   := Relation.ReflTransGen

namespace Star

open Relation

alias head   := ReflTransGen.head
alias trans  := ReflTransGen.trans
alias refl   := ReflTransGen.refl
alias single := ReflTransGen.single
alias lift   := ReflTransGen.lift
alias head_induction_on := ReflTransGen.head_induction_on

end Star
