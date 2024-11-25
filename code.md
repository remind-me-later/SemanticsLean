# Semantics in Lean 4

## Implementation of various proofs of semantics of programming languages in Lean

## Code structure

```sh
Semantics
├── Imp
│   ├── Aexp.lean
│   ├── Bexp.lean
│   ├── Denotational.lean
│   ├── Equivalence.lean
│   ├── Lang.lean
│   ├── Natural.lean
│   └── Structural.lean
├── KnasterTarski.lean
├── Maps.lean
├── ReflTransRel.lean
└── Set.lean
```

### Set.lean

```lean
-- # Sets

def Set (α: Type u) := α → Prop

def setOf (p: α → Prop): Set α :=
  p

namespace Set

protected def Mem (s: Set α) (a: α): Prop :=
  s a

instance: Membership α (Set α) :=
  ⟨Set.Mem⟩

theorem ext {a b: Set α} (h: ∀ (x: α), x ∈ a ↔ x ∈ b):
  a = b :=
  funext (λ x ↦ propext (h x))

protected def Subset (s₁ s₂: Set α) :=
  ∀ {{a}}, a ∈ s₁ → a ∈ s₂

instance: LE (Set α) :=
  ⟨Set.Subset⟩

instance: HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩

instance: EmptyCollection (Set α) :=
  ⟨λ _ ↦ False⟩

notation (priority := high) "{" x " | " p "}" => setOf (λ x => p)

def univ: Set α := {_a | True}

protected def insert (a: α) (s: Set α): Set α :=
  {b | b = a ∨ b ∈ s}

instance: Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a: α): Set α := {b | b = a}

instance instSingletonSet: Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (s₁ s₂: Set α): Set α := {a | a ∈ s₁ ∨ a ∈ s₂}

instance: Union (Set α) := ⟨Set.union⟩

protected def inter (s₁ s₂: Set α): Set α := {a | a ∈ s₁ ∧ a ∈ s₂}

instance: Inter (Set α) := ⟨Set.inter⟩

protected def compl (s: Set α): Set α := {a | a ∉ s}

protected def diff (s t: Set α): Set α := {a | a ∈ s ∧ a ∉ t}

instance: SDiff (Set α) := ⟨Set.diff⟩

end Set

/-
  ## Set theorems
-/

theorem Set.mem_comprehend
  (a: α) (P: α → Prop):
  a ∈ ({a | P a}: Set α) ↔ P a :=
  Iff.rfl

theorem Set.mem_diff {s t: Set α}
  (x: α): x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

/-
  ### Basic subset properties
-/

theorem Subset.refl
  (x: Set α): x ⊆ x :=
  λ _ => id

theorem Subset.trans {x y z: Set α}
  (h₁: x ⊆ y) (h₂: y ⊆ z): x ⊆ z :=
  λ _ h => h₂ (h₁ h)

theorem Subset.antisymm {x y: Set α}
  (hsub₁: x ⊆ y) (hsub₂: y ⊆ x): x = y :=
  funext λ _ => propext ⟨(hsub₁ ·), (hsub₂ ·)⟩

theorem Subset.from_eq {x y: Set α}
  (heq: x = y): x ⊆ y :=
  λ _ h₁ => heq ▸ h₁

/-
  ### Set if then else
-/

def Set.ite (t s s': Set α): Set α :=
  s ∩ t ∪ s' \ t

theorem Set.ite_mono (t: Set α) {s₁ s₁' s₂ s₂': Set α}
  (h: s₁ ⊆ s₂) (h': s₁' ⊆ s₂'):
  t.ite s₁ s₁' ⊆ t.ite s₂ s₂' := λ _ h2 =>
  match h2 with
  | Or.inl ⟨hl, hr⟩ => Or.inl ⟨h hl, hr⟩
  | Or.inr ⟨hl, hr⟩ => Or.inr ⟨h' hl, hr⟩

/-
  ## Set theoretic (partial) functions

  Really these are just relations, but we can think of them as functions
-/

namespace SFun

notation:20 α " →ˢ " β => Set (α × β)

def id: α →ˢ α := {p | p.1 = p.2}

theorem mem_id: (a, b) ∈ id ↔ a = b :=
  Iff.rfl

def comp (f g: α →ˢ α): α →ˢ α :=
  {x | ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g}

infixl:90 " ○ " => SFun.comp

theorem mem_comp {f g: α →ˢ α}:
  x ∈ f ○ g ↔ ∃z, (x.1, z) ∈ f ∧ (z, x.2) ∈ g :=
  Iff.rfl

theorem comp_mono {α: Type} {f g h k: Set (α × α)}
  (hfh: f ⊆ h) (hgk: g ⊆ k): f ○ g ⊆ h ○ k :=
  λ _ ⟨z, h₁, h₂⟩ => ⟨z, hfh h₁, hgk h₂⟩

theorem comp_id {f: α →ˢ α}: f ○ id = f := by
  funext (_s₁, s₂)
  apply eq_iff_iff.mpr
  unfold comp
  constructor
  . intro ⟨z, h₁, h₂⟩
    apply mem_id.mp h₂ ▸ h₁
  . intro h
    exact ⟨s₂, h, rfl⟩

theorem id_comp {f: α →ˢ α}: id ○ f = f := by
  funext (s₁, _s₂)
  apply eq_iff_iff.mpr
  unfold comp
  constructor
  . intro ⟨z, h₁, h₂⟩
    apply mem_id.mp h₁ ▸ h₂
  . intro h
    exact ⟨s₁, rfl, h⟩

end SFun
```

### ReflTransRel.lean

```lean
-- Reflexive transitive relations
inductive RTL (r : α → α → Prop) (a : α) : α → Prop
  | refl : RTL r a a
  | tail : RTL r a b → r b c → RTL r a c

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
    · exact λ h1 h2 => head h1 (h2.tail hbc)

theorem lift {r: α → α → Prop} {p : β → β → Prop} {a b : α} (f : α → β)
    (h : ∀ a b, r a b → p (f a) (f b)) (hab : RTL r a b) : RTL p (f a) (f b) := by
  induction hab with
  | refl => exact refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

end RTL
```

### Maps.lean

```lean
/-
# Maps
-/

/-
## Total maps
-/

def TotalMap A := String → A

def TotalMap.default (v: A): TotalMap A := λ _ => v

def TotalMap.update (m: TotalMap A) (k: String) (v: A) :=
  λ k' => bif k == k' then v else m k'

notation m "[" k " ← " v "]" => TotalMap.update m k v

namespace TotalMap

theorem eval:
  (m[k ← v]) k = v := by
  unfold TotalMap.update
  rw [beq_self_eq_true, cond_true]

theorem eval_neq (hneq: k != k'):
  (m[k ← v]) k' = m k' := by
  unfold TotalMap.update
  rw [bne_iff_ne] at hneq
  rw [Bool.cond_neg]
  rw [beq_eq_false_iff_ne k k']
  exact hneq

theorem eval_last:
  m[k ← v₂][k ← v₁] = m[k ← v₁] := by
  funext k'
  match h: k == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true, cond_true]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false, cond_false, cond_false]

theorem eval_swap (hneq : k₁ != k₂):
  m[k₂ ← v₂][k₁ ← v₁] = m[k₁ ← v₁][k₂ ← v₂] := by
  funext k'
  match h: k₁ == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true]
    match h': k₂ == k' with
    | true =>
      rw [eq_of_beq h, eq_of_beq h', bne_iff_ne] at hneq
      contradiction
    | false =>
      rw [cond_false, cond_true]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false, cond_false]

theorem eval_id:
  m[k ← m k] = m := by
  funext k'
  match h: k == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true, eq_of_beq h]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false]

theorem eval_same:
  (λ _ => v)[k ← v] = λ _ => v := by
  funext k'
  match h: k == k' with
  | true =>
    unfold TotalMap.update
    rw [h, cond_true]
  | false =>
    unfold TotalMap.update
    rw [h, cond_false]

example (m: TotalMap Nat):
  m["a" ← 0]["a" ← 2] = m["a" ← 2] := eval_last

example (m: TotalMap Nat):
  m["a" ← 0]["b" ← 2] = m["b" ← 2]["a" ← 0] := by
  apply eval_swap
  simp only [String.reduceBNe]

example (m: TotalMap Nat):
  m["a" ← m "a"]["b" ← 0] = m["b" ← 0] := eval_id ▸ rfl

end TotalMap

/-
## Partial maps
-/

def PartialMap A := TotalMap (Option A)

def PartialMap.default: PartialMap A := TotalMap.default none
```

### KnasterTarski.lean

```lean
import Semantics.Set

-- Concrete Semantics with Isabelle
-- 10.4.1 The Knaster-Tarski Fixpoint Theorem on Sets

-- define a partial order
class PartialOrder (α: Type) extends LE α, LT α where
  le_refl: ∀ a: α, a ≤ a
  le_trans: ∀ a b c: α, a ≤ b → b ≤ c → a ≤ c
  le_iff_le_not_le: ∀ a b: α, a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_antisymm: ∀ a b: α, a ≤ b → b ≤ a → a = b

theorem PartialOrder.le_rfl [PartialOrder α] {a: α}:
  a ≤ a :=
  le_refl a

theorem Set.le_def (a b : Set α) :
  a ≤ b ↔ a ⊆ b := Iff.rfl

instance Set.LT (α: Type): LT (Set α) :=
  {
    lt := λ a b => a ⊆ b ∧ a ≠ b
  }

theorem Set.lt_def (a b : Set α):
  a < b ↔ a ⊆ b ∧ a ≠ b :=
  Iff.rfl

instance Set.partialOrder: PartialOrder (Set α) :=
  {
    le := λ a b => a ⊆ b,
    lt := λ a b => a ⊆ b ∧ a ≠ b,
    le_refl := λ _ _ ha => ha,
    le_antisymm := λ _ _ h₁ h₂ => Subset.antisymm h₁ h₂,
    le_iff_le_not_le := by {
      intro _ _
      constructor
      . intro ⟨h₁, h₂⟩
        exact ⟨h₁, λ h' => h₂ $ Subset.antisymm h₁ h'⟩
      . intro ⟨h₁, h₂⟩
        exact ⟨h₁, λ h' => h₂ $ Subset.from_eq h'.symm⟩
    }
    le_trans := λ _ _ _ h₁ h₂ _ ha => h₂ (h₁ ha)
  }

class CompleteLattice (α: Type) extends PartialOrder α where
  Inf: Set α → α
  Inf_le: ∀ s: Set α, ∀x ∈ s, Inf s ≤ x
  le_Inf: ∀ (s: Set α) (a: α), (∀ b ∈ s, a ≤ b) → a ≤ Inf s

theorem inf_unique [CompleteLattice α]
  (s: Set α) (a b: α)
  (h: CompleteLattice.Inf s = a) (h': CompleteLattice.Inf s = b):
  a = b :=
  PartialOrder.le_antisymm _ _
    (h ▸ h' ▸ PartialOrder.le_refl b)
    (h' ▸ h ▸ PartialOrder.le_refl a)

instance Set.completeLattice: CompleteLattice (Set α) :=
  {
    Inf := λ s => {x | ∀ A ∈ s, x ∈ A},
    Inf_le := λ _ x hx _ ha => ha x hx,
    le_Inf := λ _ _ h _ hb _ hd => h _ hd hb
  }

/-
## Least Fixed Points
-/

namespace Fix

def lfp [CompleteLattice α]
  (f: α → α): α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le [CompleteLattice α] {f: α → α}
  (h: f a ≤ a):
  lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp [CompleteLattice α] {f: α → α}
  (h: ∀a', f a' ≤ a' → a ≤ a'):
  a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

end Fix

/-
## Monotonic Functions
-/

def monotone [PartialOrder α] [PartialOrder β]
  (f: α → β): Prop :=
  ∀a b, a ≤ b → f a ≤ f b

theorem monotone_id [PartialOrder α]:
  monotone (λ a: α => a) := λ _ _ h => h

theorem monotone_const [PartialOrder α] [PartialOrder β]
  (b: β):
  monotone (λ _: α => b) := λ _ _ _ => PartialOrder.le_refl b

theorem monotone_union [PartialOrder α]
  (f g: α → Set β) (hf: monotone f) (hg: monotone g):
  monotone (λ a => f a ∪ g a) := by
  intro a a' ha b hb
  match hb with
  | Or.inl h => exact Or.inl (hf a a' ha h)
  | Or.inr h => exact Or.inr (hg a a' ha h)

/-
## The Knaster-Tarski Fixpoint Theorem
-/

namespace Fix

theorem lfp_eq [CompleteLattice α] (f: α → α)
    (hf: monotone f): lfp f = f (lfp f) :=
  let h: f (lfp f) ≤ lfp f :=
    le_lfp (λ a h => PartialOrder.le_trans _ _ _ (hf _ a $ lfp_le h) h)
  PartialOrder.le_antisymm _ _ (lfp_le $ hf _ _ h) h

end Fix
```

### Imp/Lang.lean

```lean
import Semantics.Maps

def State := TotalMap Int
def s₀: State := TotalMap.default 0

#eval s₀ "x"
#eval (s₀["x" ← 3]["x" ← 4]) "x"
#eval (s₀["x" ← 3]["x" ← 4]["x" ← 7]) "x"

example: s₀["x" ← 3] = s₀["x" ← 4]["x" ← 3] := TotalMap.eval_last.symm

inductive Aexp where
  | val₁ : Int → Aexp
  | var₁ : String → Aexp
  -- arithmetic
  | add₁ : Aexp → Aexp → Aexp
  | sub₁ : Aexp → Aexp → Aexp
  | mul₁ : Aexp → Aexp → Aexp

instance: OfNat Aexp n := ⟨Aexp.val₁ n⟩
instance: Add Aexp := ⟨Aexp.add₁⟩
instance: Sub Aexp := ⟨Aexp.sub₁⟩
instance: Neg Aexp := ⟨λ a => Aexp.sub₁ 0 a⟩
instance: Mul Aexp := ⟨Aexp.mul₁⟩

-- x + 3
#check Aexp.var₁ "x" + 3

-- x * -3
#check Aexp.var₁ "x" * -3

inductive Bexp where
  -- constants
  | true₁
  | false₁
  -- boolean
  | not₁ : Bexp → Bexp
  | and₁ : Bexp → Bexp → Bexp
  | or₁  : Bexp → Bexp → Bexp
  -- comparison
  | eq₁ : Aexp → Aexp → Bexp
  | le₁ : Aexp → Aexp → Bexp

instance: Complement Bexp := ⟨Bexp.not₁⟩
instance: AndOp Bexp := ⟨Bexp.and₁⟩
instance: OrOp Bexp := ⟨Bexp.or₁⟩

-- !(x <= 3)
#check ~~~(Bexp.le₁ (Aexp.var₁ "x") 3)

inductive Com where
  | skip₁
  | cat₁   : Com → Com → Com
  | ass₁   : String → Aexp → Com
  | if₁    : Bexp → Com → Com → Com
  | while₁ : Bexp → Com → Com

instance: Append Com := ⟨Com.cat₁⟩

/-
## Syntax
-/
-- Meta syntax
notation "if " c " then " a " else " b " end" => Com.if₁ c a b
notation "while " c " loop " a " end" => Com.while₁ c a

declare_syntax_cat imp

-- general
syntax "(" imp ")" : imp
-- aexp
syntax num: imp
syntax ident: imp
syntax:55 imp:55 "*" imp:56 : imp
syntax:60 imp:60 "+" imp:61 : imp
syntax:60 imp:60 "-" imp:61 : imp
-- bexp
syntax:65 imp:65 "&&" imp:66 : imp
syntax:65 imp:65 "||" imp:66 : imp
syntax:70 imp:70 "==" imp:71 : imp
syntax:70 imp:70 "<=" imp:71 : imp
syntax:80 "!" imp:81 : imp
-- com
syntax:40 imp:40 ";" imp:41 : imp
syntax:50 imp:50 "=" imp:51 : imp
syntax "if" imp "then" imp "else" imp "end" : imp
syntax "while" imp "loop" imp "end" : imp
-- meta
syntax "[|" imp "|]" : term

macro_rules
  -- keywords
  | `([|skip|]) => `(Com.skip₁)
  | `([|true|]) => `(Bexp.true₁)
  | `([|false|]) => `(Bexp.false₁)
  -- general
  | `([|($x)|]) => `([|$x|])
  -- aexp
  | `([|$x:ident|]) => `(Aexp.var₁ $(Lean.quote (toString x.getId)))
  | `([|$n:num|])   => `($n)
  | `([|$x + $y|])  => `([|$x|] + [|$y|])
  | `([|$x - $y|])  => `([|$x|] - [|$y|])
  | `([|$x * $y|])  => `([|$x|] * [|$y|])
  -- bexp
  | `([|!$x|])      => `(~~~[|$x|])
  | `([|$x && $y|]) => `([|$x|] &&& [|$y|])
  | `([|$x || $y|]) => `([|$x|] ||| [|$y|])
  | `([|$x == $y|]) => `(Bexp.eq₁ [|$x|] [|$y|])
  | `([|$x <= $y|]) => `(Bexp.le₁ [|$x|] [|$y|])
  -- com
  | `([|$x:ident = $y|]) => `(Com.ass₁ $(Lean.quote (toString x.getId)) [|$y|])
  | `([|$x ; $y|])       => `(Com.cat₁ [|$x|] [|$y|])
  | `([|if $b then $x else $y end|]) => `(Com.if₁ [|$b|] [|$x|] [|$y|])
  | `([|while $b loop $x end|]) => `(Com.while₁ [|$b|] [|$x|])

#check
[|
n = 5; i = 2; res = 1;

while i <= n loop
    res = res * i;
    i = i + 1
end
|]

def Config := Com × State
```

### Imp/Aexp.lean

```lean
import Semantics.Imp.Lang

namespace Aexp
namespace Natural

private inductive step: Aexp × State → Int → Prop
  | valₙ: step (val₁ n, _) n
  | varₙ: step (var₁ v, s) (s v)
  | addₙ (ha₁: step (a₁, s) n₁) (ha₂: step (a₂, s) n₂):
    step (a₁ + a₂, s) (n₁ + n₂)
  | subₙ (ha₁: step (a₁, s) n₁) (ha₂: step (a₂, s) n₂):
    step (a₁ - a₂, s) (n₁ - n₂)
  | mulₙ (ha₁: step (a₁, s) n₁) (ha₂: step (a₂, s) n₂):
    step (a₁ * a₂, s) (n₁ * n₂)

infix:10 " ⟹ₐ " => step

private instance step.equiv: Setoid Aexp where
  r a₁ a₂ := ∀s n, ((a₁, s) ⟹ₐ n) = ((a₂, s) ⟹ₐ n)
  iseqv := {
    refl := λ _ _ _ => rfl
    symm := λ h s n => (h s n).symm
    trans := λ h₁ h₂ s n => (h₁ s n) ▸ (h₂ s n)
  }

end Natural

def reduce (a: Aexp) (s: State): Int :=
  match a with
  | val₁ a => a
  | var₁ a => s a
  | add₁ a₁ a₂ => a₁.reduce s + a₂.reduce s
  | sub₁ a₁ a₂ => a₁.reduce s - a₂.reduce s
  | mul₁ a₁ a₂ => a₁.reduce s * a₂.reduce s

instance: CoeFun Aexp (λ _ => State → Int) := ⟨reduce⟩

instance reduce.equiv: Setoid Aexp where
  r a₁ a₂ := ∀s, a₁ s = a₂ s
  iseqv := {
    refl := λ _ _ => rfl
    symm := λ h s => (h s).symm
    trans := λ h₁ h₂ s => (h₁ s) ▸ (h₂ s)
  }

section Equivalence

-- relational definition is equal to recursive
private theorem reduce.from_natural
  (hstep: conf ⟹ₐ n): conf.1 conf.2 = n :=
  by induction hstep with
  | addₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | subₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | mulₙ _ _ iha₁ iha₂ => exact iha₁ ▸ iha₂ ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce
  (hred: a s = n): (a, s) ⟹ₐ n :=
  by induction a generalizing n with
  | val₁ a => exact hred ▸ step.valₙ
  | var₁ a => exact hred ▸ step.varₙ
  | add₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ step.addₙ (iha₁ rfl) (iha₂ rfl)
  | sub₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ step.subₙ (iha₁ rfl) (iha₂ rfl)
  | mul₁ a₁ a₂ iha₁ iha₂ =>
    exact hred ▸ step.mulₙ (iha₁ rfl) (iha₂ rfl)

private theorem step_eq_reduce:
  ((a, s) ⟹ₐ n) = (a s = n) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

private theorem step_eq_reduce':
  (a, s) ⟹ₐ a s :=
  Natural.from_reduce rfl

private theorem step_eq_eq_reduce_eq:
  Natural.step.equiv.r a₁ a₂ ↔ reduce.equiv.r a₁ a₂ := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    specialize h s (a₂ s)
    rw [step_eq_reduce, step_eq_reduce, eq_self, iff_true] at h
    exact h
  . intro h s _
    rw [step_eq_reduce, step_eq_reduce]
    specialize h s
    rw [h]

end Equivalence

end Aexp
```

### Imp/Bexp.lean

```lean
import Semantics.Imp.Aexp

namespace Bexp
namespace Natural

-- Operational semantics of Bexp
private inductive step: Bexp × State → Bool → Prop
  | trueₙ: step (true₁, _) true
  | falseₙ: step (false₁, _) false
  | notₙ (h: step (b, s) n):
    step (~~~b, s) (!n)
  | andₙ (h₁: step (b₁, s) n₁) (h₂: step (b₂, s) n₂):
    step (b₁ &&& b₂, s) (n₁ && n₂)
  | orₙ (h₁: step (b₁, s) n₁) (h₂: step (b₂, s) n₂):
    step (b₁ ||| b₂, s) (n₁ || n₂)
  | eqₙ: step (eq₁ a₁ a₂, s) (a₁ s == a₂ s)
  | leₙ: step (le₁ a₁ a₂, s) (a₁ s <= a₂ s)

infix:10 " ⟹ₗ " => step

private instance step.equiv: Setoid Bexp where
  r b₁ b₂ := ∀s n, ((b₁, s) ⟹ₗ n) = ((b₂, s) ⟹ₗ n)
  iseqv := {
    refl := λ _ _ _ => rfl
    symm := λ h s n => (h s n).symm
    trans := λ h₁ h₂ s n => (h₁ s n) ▸ (h₂ s n)
  }

end Natural

-- Denotational semantics of Bexp
def reduce (b: Bexp) (s: State): Bool :=
  match b with
  | true₁  => true
  | false₁ => false
  | not₁ b => !b.reduce s
  | and₁ b₁ b₂ => b₁.reduce s && b₂.reduce s
  | or₁ b₁ b₂  => b₁.reduce s || b₂.reduce s
  | eq₁ a₁ a₂  => a₁ s == a₂ s
  | le₁ a₁ a₂  => a₁ s <= a₂ s

instance: CoeFun Bexp (λ _ => State → Bool) := ⟨reduce⟩

instance reduce.equiv: Setoid Bexp where
  r b₁ b₂:= ∀s, b₁ s = b₂ s
  iseqv := {
    refl := λ _ _ => rfl
    symm := λ h s => (h s).symm
    trans := λ h₁ h₂ s => (h₁ s) ▸ (h₂ s)
  }

section Equivalence

-- relational definition is equivalent to recursive
private theorem reduce.from_natural
  (hstep: conf ⟹ₗ x): conf.1 conf.2 = x :=
  by induction hstep with
  | notₙ _ ih => exact ih ▸ rfl
  | andₙ _ _ ihb₁ ihb₂ | orₙ _ _ ihb₁ ihb₂ =>
    exact ihb₁ ▸ ihb₂ ▸ rfl
  | _ => rfl

private theorem Natural.from_reduce
  (hred: b s = x): (b, s) ⟹ₗ x :=
  by induction b generalizing x with
  | true₁ => exact hred ▸ step.trueₙ
  | false₁ => exact hred ▸ step.falseₙ
  | not₁ _ ih => exact hred ▸ step.notₙ (ih rfl)
  | and₁ _ _ ihb₁ ihb₂ =>
    exact hred ▸ step.andₙ (ihb₁ rfl) (ihb₂ rfl)
  | or₁ _ _ ihb₁ ihb₂ =>
    exact hred ▸ step.orₙ (ihb₁ rfl) (ihb₂ rfl)
  | eq₁ => exact hred ▸ step.eqₙ
  | le₁ => exact hred ▸ step.leₙ

private theorem step_eq_reduce:
  ((b, s) ⟹ₗ x) = (b s = x) :=
  propext ⟨reduce.from_natural, Natural.from_reduce⟩

private theorem step_eq_reduce':
  (b, s) ⟹ₗ b s :=
  Natural.from_reduce rfl

private theorem not_true_eq_false:
  (!(reduce b s)) = (~~~b) s :=
  rfl

private theorem step_eq_eq_reduce_eq:
  Natural.step.equiv.r b₁ b₂ ↔ reduce.equiv.r b₁ b₂ := by
  simp only [Setoid.r, eq_iff_iff]
  constructor
  . intro h s
    exact (step_eq_reduce ▸ h s (b₂ s)).mpr $ step_eq_reduce.mpr rfl
  . intro h s _
    constructor
    . intro h1
      exact ((h s) ▸ (step_eq_reduce ▸ h1)) ▸ step_eq_reduce'
    . intro h1
      exact ((h s) ▸ (step_eq_reduce ▸ h1)) ▸ step_eq_reduce'

end Equivalence

end Bexp
```

### Imp/Denotational.lean

```lean
import Semantics.Imp.Bexp
import Semantics.KnasterTarski

/-
# Relational denotational semantics

From Concrete semantics with Isabelle
-/

namespace Com

def denote_while (b: Bexp) (f: State →ˢ State):
  (State →ˢ State) → (State →ˢ State) :=
  λ g => Set.ite {(s, _) | b s} (f ○ g) SFun.id

def denote: Com → (State →ˢ State)
  | skip₁      => SFun.id
  | ass₁ v a   => {(s, t) | t = s[v ← a s]}
  | cat₁ c₁ c₂ => c₁.denote ○ c₂.denote
  | if b then c₁ else c₂ end =>
      Set.ite {(s, _) | b s} c₁.denote c₂.denote
  | while b loop c end =>
      Fix.lfp $ denote_while b c.denote

theorem monotone_denote_loop: monotone (denote_while b c) :=
  λ _ _ hmp =>
  Set.ite_mono _ (SFun.comp_mono PartialOrder.le_rfl hmp) PartialOrder.le_rfl

notation (priority := high) "⟦" c "⟧" => denote c

#check (s₀, s₀["x"←5]["x"←1]) ∈ ⟦[|x = 5; if x <= 1 then skip else x = 1 end|]⟧
#check (s₀, s₀["x"←5]) ∈ ⟦[|x = 5; while x <= 1 loop x = 1 end|]⟧

namespace denote

instance equiv: Setoid Com where
  r a b := ⟦a⟧ = ⟦b⟧
  iseqv := {
    refl := λ _ => rfl,
    symm := Eq.symm
    trans := Eq.trans
  }

theorem skipl:
  (skip₁++c) ≈ c := by
  simp only [HasEquiv.Equiv, equiv, denote, SFun.id_comp]

theorem skipr:
  (c++skip₁) ≈ c := by
  simp only [HasEquiv.Equiv, equiv, denote, SFun.comp_id]

theorem while_unfold:
  while b loop c end ≈ if b then c++ while b loop c end else skip₁ end :=
  Fix.lfp_eq _ monotone_denote_loop

/-
## Congruence
-/

theorem cat_congr {c₁ c₂ d₁ d₂: Com}
  (hc: c₁ ≈ c₂) (hd: d₁ ≈ d₂):
  (c₁++d₁) ≈ (c₂++d₂) := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem cond_congr (hc: c1 ≈ c2) (hd: d1 ≈ d2):
  if b then c1 else d1 end ≈ if b then c2 else d2 end := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ hd ▸ rfl

theorem loop_congr (hc: c1 ≈ c2):
  while b loop c1 end ≈ while b loop c2 end := by
  simp only [HasEquiv.Equiv, equiv, denote]
  exact hc ▸ rfl

end denote
end Com
```

### Imp/Equivalence.lean

```lean
import Semantics.Imp.Natural
import Semantics.Imp.Structural
import Semantics.Imp.Denotational

namespace Com

theorem Structural.from_natural
  (hconf: conf ⟹ s₂): conf ⇒* (skip₁, s₂) := by
  induction hconf with
  | skipₙ => exact RTL.refl
  | assₙ => exact RTL.single step.assₛ
  | catₙ _ _ _ ihc₁ ihc₂ => exact star.cat ihc₁ ihc₂
  | if₁ₙ hb _ ih => exact RTL.head step.ifₛ (hb ▸ ih)
  | if₀ₙ hb _ ih => exact RTL.head step.ifₛ (hb ▸ ih)
  | while₁ₙ _ hb _ _ ihc ihw =>
    exact RTL.head step.whileₛ $ RTL.trans (hb ▸ star.cat ihc ihw) RTL.refl
  | while₀ₙ hb =>
    exact RTL.head step.whileₛ $ hb ▸ RTL.refl

theorem Natural.from_structural_step
  (hconf₁: conf₁ ⇒ conf₂) (hconf₂: conf₂ ⟹ s₂): conf₁ ⟹ s₂ := by
  induction hconf₁ generalizing s₂ with
  | assₛ => exact (skip_eq.mp hconf₂) ▸ step.assₙ
  | cat₀ₛ => exact step.catₙ _ step.skipₙ hconf₂
  | catₙₛ _ ih =>
    match hconf₂ with
    | step.catₙ s₂ hc₁ hc₂ => exact step.catₙ s₂ (ih hc₁) hc₂
  | ifₛ => exact if_eq' ▸ hconf₂
  | whileₛ => rw [loop_unfold]; exact if_eq' ▸ hconf₂

theorem Natural.from_structural
  (hconf: conf ⇒* (skip₁, s₂)): conf ⟹ s₂ := by
  induction hconf using RTL.head_induction_on with
  | refl => exact step.skipₙ
  | head hsingle _ hs₂ => exact from_structural_step hsingle hs₂

theorem structural_eq_natural:
  ((c₁, s₁) ⇒* (skip₁, s₂)) = ((c₁, s₁) ⟹ s₂) :=
  propext ⟨Natural.from_structural, Structural.from_natural⟩

theorem denote.from_natural
  (hconf: conf ⟹ s₃): (conf.2, s₃) ∈ ⟦conf.1⟧ := by
  induction hconf with
  | skipₙ => exact SFun.mem_id.mpr rfl
  | assₙ  => exact SFun.mem_id.mpr rfl
  | catₙ s₂ _ _ ih₁ ih₂ => exact ⟨s₂, ih₁, ih₂⟩
  | if₁ₙ hb _ ih => exact Or.inl ⟨ih, hb⟩
  | if₀ₙ hb _ ih =>
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hb,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      exact ih
  | while₁ₙ s₂ hb _ _ ih₁ ih₂ =>
    exact while_unfold ▸ Or.inl ⟨⟨s₂, ih₁, ih₂⟩, hb⟩
  | while₀ₙ hb =>
      rw [while_unfold]
      apply Or.inr
      simp only [Set.mem_diff, Set.mem_comprehend, hb,
                  Bool.false_eq_true, not_false_eq_true,
                  and_true]
      rfl

theorem Natural.from_denote
  (hmem: (s₁, s₃) ∈ ⟦c⟧): (c, s₁) ⟹ s₃ := by
  revert hmem
  induction c generalizing s₁ s₃ with
  | skip₁ =>
    intro hmp
    rw [denote, SFun.mem_id] at hmp
    exact hmp ▸ step.skipₙ
  | ass₁ =>
    intro hmp
    rw [denote.eq_def, Set.mem_comprehend] at hmp
    simp only at hmp
    exact hmp ▸ step.assₙ
  | cat₁ _ _ ih₁ ih₂ =>
    intro ⟨s₂, h₁, h₂⟩
    exact step.catₙ s₂ (ih₁ h₁) (ih₂ h₂)
  | if₁ _ _ _ ih₁ ih₂ =>
    intro hmp
    match hmp with
    | Or.inl ⟨h₁, hb⟩ =>
      exact step.if₁ₙ hb (ih₁ h₁)
    | Or.inr ⟨h₁, hb⟩ =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hb
      exact step.if₀ₙ hb (ih₂ h₁)
  | while₁ b c ih =>
    suffices
      ⟦while b loop c end⟧ ⊆ {(s₁, s₃) | (while b loop c end, s₁) ⟹ s₃} by
      apply this

    apply Fix.lfp_le
    intro ⟨_, _⟩ hmp
    match hmp with
    | Or.inl ⟨⟨s₂, h₁, h₂⟩, hb⟩ =>
      exact step.while₁ₙ s₂ hb (ih h₁) h₂
    | Or.inr ⟨hid, hb⟩ =>
      simp only [Set.mem_comprehend, Bool.not_eq_true] at hb
      rw [SFun.mem_id] at hid
      exact hid ▸ step.while₀ₙ hb

theorem natural_eq_denote: ((s₁, s₂) ∈ ⟦c⟧) = ((c, s₁) ⟹ s₂) :=
  propext ⟨Natural.from_denote, denote.from_natural⟩

theorem structural_eq_denote:
  ((c, s₁) ⇒* (skip₁, s₂)) = ((s₁, s₂) ∈ ⟦c⟧) :=
  by rw [structural_eq_natural, natural_eq_denote]

end Com
```

### Imp/Natural.lean

```lean
import Semantics.Imp.Bexp

namespace Com
namespace Natural

inductive step: Config → State → Prop
  | skipₙ:
    step (skip₁, s) s

  | assₙ:
    step (ass₁ v a, s) (s[v ← a s])

  | catₙ (s₂: State) (hc₁: step (c₁, s₁) s₂) (hc₂: step (c₂, s₂) s₃):
    step (c₁++c₂, s₁) s₃

  | if₀ₙ (hb: b s₁ = false) (hc₂: step (c₂, s₁) s₂):
    step (if b then c₁ else c₂ end, s₁) s₂

  | if₁ₙ (hb: b s₁ = true) (hc₁: step (c₁, s₁) s₂):
    step (if b then c₁ else c₂ end, s₁) s₂

  | while₀ₙ (hb: b s₁ = false):
    step (while b loop c end, s₁) s₁

  | while₁ₙ
    (s₂: State) (hb: b s₁ = true) (hc: step (c, s₁) s₂)
    (hw: step (while b loop c end, s₂) s₃):
    step (while b loop c end, s₁) s₃

infix:10 " ⟹ " => step

private example:  ([|x = 5|], s₀) ⟹ s₀["x" ← 5] := step.assₙ

private example:
   ([|
      x = 2;
      if x <= 1 then
        y = 3
      else
        z = 4
      end
    |], s₀)
    ⟹ s₀["x" ← 2]["z" ← 4] :=
    step.catₙ _ step.assₙ $ step.if₀ₙ rfl step.assₙ

private example:
  ([| x = 2; x = 3|], s₀) ⟹ s₀["x" ← 3] :=
  let h1: s₀["x" ← 3] = s₀["x" ← 2]["x" ← 3] :=
    TotalMap.eval_last.symm
  h1 ▸ step.catₙ _ step.assₙ step.assₙ

/-
## Rewriting rules
-/

theorem skip_eq:
  ((skip₁, s₁) ⟹ s₂) = (s₁ = s₂) :=
  propext {
    mp := λ (step.skipₙ) => rfl,
    mpr := (· ▸ step.skipₙ)
  }

theorem cat_eq:
  ((c₁++c₂, s₁) ⟹ s₃) = ∃s₂, ((c₁, s₁) ⟹ s₂) ∧ ((c₂, s₂) ⟹ s₃) :=
  propext {
    mp := λ (step.catₙ s₂ h₁ h₂) => ⟨s₂, h₁, h₂⟩,
    mpr := λ ⟨s₂, h₁, h₂⟩ => step.catₙ s₂ h₁ h₂
  }

theorem if_eq:
  ((if b then c₁ else c₂ end, s₁) ⟹ s₂)
    = bif b s₁ then (c₁, s₁) ⟹ s₂ else (c₂, s₁) ⟹ s₂ :=
  propext {
    mp := λ hmp => match hmp with
      | step.if₁ₙ hb h | step.if₀ₙ hb h => hb ▸ h,
    mpr := match hb: b s₁ with
      | true => λ hmp => step.if₁ₙ hb hmp
      | false => λ hmp => step.if₀ₙ hb hmp
  }

theorem if_eq':
  ((if b then c₁ else c₂ end, s₁) ⟹ s₂)
    = ((bif b s₁ then c₁ else c₂, s₁) ⟹ s₂) :=
  propext {
    mp := λ hmp => match hmp with
      | step.if₁ₙ hb h | step.if₀ₙ hb h => hb ▸ h,
    mpr := match hb: b s₁ with
      | true => λ hmp => step.if₁ₙ hb hmp
      | false => λ hmp => step.if₀ₙ hb hmp
  }

theorem while_eq:
  ((while b loop c end, s₁) ⟹ s₃) =
    bif b s₁ then
      ∃s₂, ((c, s₁) ⟹ s₂) ∧ ((while b loop c end, s₂) ⟹ s₃)
    else
      s₁ = s₃ :=
  propext {
    mp := λ hmp => match hmp with
      | step.while₁ₙ s₂ hb hc hw => hb ▸ ⟨s₂, hc, hw⟩
      | step.while₀ₙ hb => hb ▸ rfl,
    mpr := match hb: b s₁ with
      | true => λ ⟨s₂, h₁, h₂⟩ => step.while₁ₙ s₂ hb h₁ h₂
      | false => λ hmp => hmp ▸ step.while₀ₙ hb
  }

/-
## Behavioral equivalence
-/

instance equiv: Setoid Com where
  r c₁ c₂ := ∀s₁ s₂, ((c₁, s₁) ⟹ s₂) ↔ ((c₂, s₁) ⟹ s₂)
  iseqv := {
    refl := λ _ _ _ => Iff.rfl
    symm := (Iff.symm $ · · ·)
    trans := λ h1 h2 x n => Iff.trans (h1 x n) (h2 x n)
  }

theorem skipl:
  (skip₁++c) ≈ c :=
  λ _ _ => {
    mp := λ (step.catₙ _ hc hd) => skip_eq.mp hc ▸ hd,
    mpr := λ h => step.catₙ _ step.skipₙ h
  }

theorem skipr:
  (c++skip₁) ≈ c :=
  λ _ _ => {
    mp := λ (step.catₙ _ hc hd) => skip_eq.mp hd ▸ hc,
    mpr := λ h => step.catₙ _ h step.skipₙ
  }

theorem cond_true (hb: b ≈ Bexp.true₁):
  if b then c₁ else c₂ end ≈ c₁ := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem cond_false (hb: b ≈ Bexp.false₁):
  if b then c₁ else c₂ end ≈ c₂ := by
  intro _ _
  rw [if_eq, hb]
  rfl

theorem loop_unfold:
  while b loop c end ≈
    if b then c++while b loop c end else skip₁ end := by
  intro s₁ s₃
  rw [if_eq']
  constructor
  . intro hmp
    match hmp with
    | step.while₁ₙ s₂ hb hc hw => exact hb ▸ step.catₙ s₂ hc hw
    | step.while₀ₙ hb => exact hb ▸ step.skipₙ
  . match hb: b s₁ with
    | false =>
      intro (step.skipₙ)
      exact step.while₀ₙ hb
    | true =>
      intro (step.catₙ s₂ hc hw)
      exact step.while₁ₙ s₂ hb hc hw

/-
## Non termination
-/

theorem loop_tt (htrue: b ≈ Bexp.true₁):
  ¬((while b loop c end, s) ⟹ t) := by
  intro hmp
  generalize hconf: (while b loop c end, s) = conf at hmp
  induction hmp generalizing s with
  | while₁ₙ _ _ _ _ _ ihw =>
    match hconf with
    | Eq.refl _ => exact ihw rfl
  | while₀ₙ hb =>
    match hconf with
    | Eq.refl _ =>
      rw [htrue] at hb
      contradiction
  | _ =>
    match Prod.mk.injEq _ _ _ _ ▸ hconf with
    | ⟨_, _⟩ => contradiction

/-
## Determinism
-/

theorem deterministic
  (hps₁: conf ⟹ s₁) (hps₂: conf ⟹ s₂): s₁ = s₂ :=
  by induction hps₁ generalizing s₂ with
  | skipₙ => match hps₂ with | step.skipₙ => rfl
  | assₙ => match hps₂ with | step.assₙ => rfl
  | catₙ _ _ _ ihc₁ ihc₂ =>
    match hps₂ with
    | step.catₙ _ hc₁ hc₂ =>
      exact ihc₂ (ihc₁ hc₁ ▸ hc₂)
  | if₁ₙ hb _ ihc₁ =>
    match hps₂ with
    | step.if₁ₙ _ hc₁ =>
      exact ihc₁ hc₁
    | step.if₀ₙ hb₁ _ =>
      rw [hb] at hb₁
      contradiction
  | if₀ₙ hb _ ihc₂ =>
    match hps₂ with
    | step.if₁ₙ hb₁ _ =>
      rw [hb] at hb₁
      contradiction
    | step.if₀ₙ _ hd =>
      exact ihc₂ hd
  | while₁ₙ _ hb _ _ ihc ihw =>
    match hps₂ with
    | step.while₁ₙ _ _ hc hw =>
      exact ihw (ihc hc ▸ hw)
    | step.while₀ₙ hb₁ =>
      rw [hb] at hb₁
      contradiction
  | while₀ₙ hb =>
    match hps₂ with
    | step.while₁ₙ _ hb₁ _ _ =>
      rw [hb] at hb₁
      contradiction
    | step.while₀ₙ _ => rfl

end Natural
end Com
```

### Imp/Structural.lean

```lean
import Semantics.Imp.Bexp
import Semantics.ReflTransRel

namespace Com
namespace Structural

inductive step: Config → Config → Prop where
  | assₛ:
    step (ass₁ v a, s) (skip₁, s[v ← a s])

  | cat₀ₛ:
    step (skip₁++c, s) (c, s)

  | catₙₛ (h: step (c₁, s₁) (c₂, s₂)):
    step (c₁++c₃, s₁) (c₂++c₃, s₂)

  | ifₛ:
    step (if b then c₁ else c₂ end, s) (bif b s then c₁ else c₂, s)

  | whileₛ:
    step (while b loop c end, s)
          (bif b s then c++while b loop c end else skip₁, s)

infixl:10 " ⇒ " => step

private example:
  ([|x = 0; while x <= 2 loop x = x + 1 end|], s₀) ⇒
      ([|skip; while x <= 2 loop x = x + 1 end|], s₀["x" ← 0]) :=
  step.catₙₛ step.assₛ

theorem cat_eq:
  ((c₁++c₃, s₁) ⇒ conf)
    = ((∃c₂ s₂, ((c₁, s₁) ⇒ (c₂, s₂)) ∧ conf = (c₂++c₃, s₂))
      ∨ (c₁ = skip₁ ∧ conf = (c₃, s₁))) :=
  propext {
    mp := λ hmp => match hmp with
      | step.cat₀ₛ => Or.inr ⟨rfl, rfl⟩
      | step.catₙₛ h => Or.inl ⟨_, _, h, rfl⟩,
    mpr := λ hmpr => match hmpr with
      | Or.inl ⟨_c₂, _s₂, h₁, h₂⟩ => h₂ ▸ step.catₙₛ h₁
      | Or.inr ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ step.cat₀ₛ
  }

theorem cond_eq:
  ((if b then c₁ else c₂ end, s) ⇒ conf)
    = (b s ∧ conf = (c₁, s) ∨ b s = false ∧ conf = (c₂, s)) :=
  propext {
    mp := λ hmp => match hb: b s with
      | false => match hmp with | step.ifₛ => Or.inr ⟨rfl, hb ▸ rfl⟩
      | true => match hmp with | step.ifₛ => Or.inl ⟨rfl, hb ▸ rfl⟩,
    mpr := λ hmpr =>
      let hss: conf = (bif b s then c₁ else c₂, s) :=
        match hb: b s with
        | true => match hb ▸ hmpr with | Or.inl ⟨_, h₂⟩ => h₂
        | false => match hb ▸ hmpr with | Or.inr ⟨_, h₂⟩ => h₂
      hss ▸ step.ifₛ
  }

theorem cond_false (hb: b s₁ = false):
  ((if b then c₁ else c₂ end, s₁) ⇒ conf) = (conf = (c₂, s₁)) :=
  propext {
    mp := λ hmp => match hb ▸ cond_eq ▸ hmp with
      | Or.inr ⟨_, h₂⟩ => h₂,
    mpr := λ hmpr => cond_eq ▸ Or.inr ⟨hb, hmpr⟩
  }

infixl:10 " ⇒* " => RTL step

theorem star.demo₂:
  ([| x = 2; while 0 <= x loop x = x + 1 end|], s₀) ⇒*
      ([| while 0 <= x loop x = x + 1 end|], s₀["x" ← 2]) :=
  RTL.head (step.catₙₛ step.assₛ) (RTL.head step.cat₀ₛ RTL.refl)

theorem star.cat_skip_cat
  (hc₁: (c₁, s₁) ⇒* (skip₁, s₂)):
  (c₁++c₂, s₁) ⇒* (skip₁++c₂, s₂) :=
  RTL.lift (λ (c₁, s) => (c₁++c₂, s)) (λ _ _ h => step.catₙₛ h) hc₁

theorem star.cat
  (hc₁: (c₁, s₁) ⇒* (skip₁, s₂))
  (hc₂: (c₂, s₂) ⇒* (skip₁, s₃)):
  (c₁++c₂, s₁) ⇒* (skip₁, s₃) :=
  RTL.trans (cat_skip_cat hc₁) (RTL.trans (RTL.single step.cat₀ₛ) hc₂)

theorem star.cat_no_influence
  (hc₁: (c₁, s) ⇒* (skip₁, s₁)):
  (c₁++c₂, s) ⇒* (c₂, s₁) :=
  RTL.trans (cat_skip_cat hc₁) (RTL.single step.cat₀ₛ)

end Structural
end Com
```