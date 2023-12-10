import Mathlib.Logic.Function.Basic

inductive Val where
  | int: Int → Val
  | nat: Nat → Val

def State := String → Val
def State.nil: State := λ _ ↦ Val.int 0

notation "⟪⟫" => State.nil
notation s "⟪" x "≔" e "⟫" => Function.update s x e

#reduce ⟪⟫ "x"
#reduce (⟪⟫⟪"x" ≔ Val.int 3⟫⟪"x" ≔ Val.int 4⟫) "x"
#reduce (⟪⟫⟪"x" ≔ Val.nat 3⟫⟪"x" ≔ Val.nat 4⟫⟪"x" ≔ Val.nat 7⟫) "x"

theorem State.demo₁: (⟪⟫⟪"x"≔Val.int 3⟫) = (⟪⟫⟪"x"≔Val.int 4⟫⟪"x"≔ Val.int 3⟫) := by simp

inductive Aexp where
  | val : Val → Aexp
  | var : String → Aexp
  | add : Aexp → Aexp → Aexp

inductive Bexp where
  | tt
  | ff
  | not : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | le  : Aexp → Aexp → Bexp

inductive Com where
  | skip
  | cat   : Com → Com → Com
  | ass   : String → Aexp → Com
  | cond  : Bexp → Com → Com → Com
  | loop  : Bexp → Com → Com

-- Meta syntax
notation:50 x:50 ";;" e:51 => Com.cat x e

-- Syntax of the language
declare_syntax_cat imp

-- general
syntax "(" imp ")" : imp
-- imp
syntax num: imp
syntax num "nat": imp
syntax ident: imp
syntax:60 imp:60 "+" imp:61 : imp
-- bexp
syntax:80 "!" imp:81 : imp
syntax:70 imp:70 "<=" imp:71 : imp
syntax:65 imp:65 "&&" imp:66 : imp
-- stmt
syntax:50 imp:50 "=" imp:51 : imp
syntax:40 imp:40 ";" imp:41 : imp
syntax "if" imp "{" imp "}" "else" "{" imp "}" : imp
syntax "while" imp "{" imp "}" : imp

-- meta
syntax "⦃" imp "⦄" : term

macro_rules
  -- keywords
  | `(⦃skip⦄) => `(Com.skip)
  | `(⦃true⦄) => `(Bexp.tt)
  | `(⦃false⦄) => `(Bexp.ff)
  -- general
  | `(⦃($x)⦄) => `(⦃$x⦄)
  -- imp
  | `(⦃$x:ident⦄) => `(Aexp.var $(Lean.quote (toString x.getId)))
  | `(⦃$n:num⦄)   => `(Aexp.val (Val.int $n))
  | `(⦃$n:num nat⦄)   => `(Aexp.val (Val.nat $n))
  | `(⦃$x + $y⦄)  => `(Aexp.add ⦃$x⦄ ⦃$y⦄)
  -- bexp
  | `(⦃!$x⦄)      => `(Bexp.not ⦃$x⦄)
  | `(⦃$x <= $y⦄)  => `(Bexp.le ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x && $y⦄)  => `(Bexp.and ⦃$x⦄ ⦃$y⦄)
  -- stmt
  | `(⦃$x:ident = $y⦄) => `(Com.ass $(Lean.quote (toString x.getId)) ⦃$y⦄)
  | `(⦃$x ; $y⦄)       => `(Com.cat ⦃$x⦄ ⦃$y⦄)
  | `(⦃if $b {$x} else {$y}⦄) => `(Com.cond ⦃$b⦄ ⦃$x⦄ ⦃$y⦄)
  | `(⦃while $b {$x}⦄) => `(Com.loop ⦃$b⦄ ⦃$x⦄)

#check ⦃z = 4; if 3 <= 2 {y = 4 + 2} else {skip}⦄
#check ⦃while true {skip}⦄
#check ⦃skip⦄
#check ⦃x = 5⦄
#check ⦃x = 5 nat + 2 nat; y = 6⦄
#check ⦃if x <= 5 {y = 6} else {z = 7}⦄
#check ⦃x = 0; while !(x <= 5) {skip; skip; x = x + 1}⦄
