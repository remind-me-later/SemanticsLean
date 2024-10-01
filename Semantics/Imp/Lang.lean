import Semantics.Maps

def State := TotalMap Int
def State.nil: State := TotalMap.default 0

notation "σ₀" => State.nil

#eval σ₀ "x"
#eval (σ₀⟪"x" ≔ 3⟫⟪"x" ≔ 4⟫) "x"
#eval (σ₀⟪"x" ≔ 3⟫⟪"x" ≔ 4⟫⟪"x" ≔ 7⟫) "x"

example: σ₀⟪"x" ≔ 3⟫ = σ₀⟪"x" ≔ 4⟫⟪"x" ≔ 3⟫ := clobber.symm

inductive Aexp where
  | val : Int → Aexp
  | var : String → Aexp
  -- arithmetic
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp

-- x + 3
#check Aexp.add (Aexp.var "x") (Aexp.val 3)

inductive Bexp where
  -- constants
  | tt
  | ff
  -- boolean
  | not : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or  : Bexp → Bexp → Bexp
  -- comparison
  | eq : Aexp → Aexp → Bexp
  | le : Aexp → Aexp → Bexp

-- !(x <= 3)
#check Bexp.not (Bexp.le (Aexp.var "x") (Aexp.val 3))

inductive Com where
  | skip
  | cat   : Com → Com → Com
  | ass   : String → Aexp → Com
  | cond  : Bexp → Com → Com → Com
  | loop  : Bexp → Com → Com

/-
## Syntax
-/
-- Meta syntax
-- aexp
notation:60 a:55 " * " b:56 => Aexp.mul a b
notation:60 a:60 " + " b:61 => Aexp.add a b
notation:60 a:60 " - " b:61 => Aexp.sub a b
-- bexp
notation:65 a:65 " && " b:66 => Bexp.and a b
notation:65 a:65 " || " b:66 => Bexp.or a b
notation:70 a:70 " == " b:71 => Bexp.eq a b
notation:70 a:70 " <= " b:71 => Bexp.le a b
notation:80 "!" a:81 => Bexp.not a
-- com
notation a:40 ";;" b:41 => Com.cat a b
notation:50 a:50 " = " b:51 => Com.ass a b
notation "if " c " then " a " else " b "end" => Com.cond c a b
notation "while " c " loop " a "end" => Com.loop c a

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
  -- aexp
  | `(⦃$x:ident⦄) => `(Aexp.var $(Lean.quote (toString x.getId)))
  | `(⦃$n:num⦄)   => `(Aexp.val $n)
  | `(⦃$x + $y⦄)  => `(Aexp.add ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x - $y⦄)  => `(Aexp.sub ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x * $y⦄)  => `(Aexp.mul ⦃$x⦄ ⦃$y⦄)
  -- bexp
  | `(⦃!$x⦄)      => `(Bexp.not ⦃$x⦄)
  | `(⦃$x && $y⦄)  => `(Bexp.and ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x || $y⦄)  => `(Bexp.or ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x == $y⦄)  => `(Bexp.eq ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x <= $y⦄)  => `(Bexp.le ⦃$x⦄ ⦃$y⦄)
  -- com
  | `(⦃$x:ident = $y⦄) => `(Com.ass $(Lean.quote (toString x.getId)) ⦃$y⦄)
  | `(⦃$x ; $y⦄)       => `(Com.cat ⦃$x⦄ ⦃$y⦄)
  | `(⦃if $b {$x} else {$y}⦄) => `(Com.cond ⦃$b⦄ ⦃$x⦄ ⦃$y⦄)
  | `(⦃while $b {$x}⦄) => `(Com.loop ⦃$b⦄ ⦃$x⦄)

#check ⦃z = 4; if 3 <= 2 {y = 4 + 2} else {skip}⦄
#check ⦃while true {skip}⦄
#check ⦃skip⦄
#check ⦃x = 5⦄
#check ⦃x = 5; y = 6⦄
#check ⦃if x <= 5 {y = 6} else {z = 7}⦄
#check ⦃x = 0; while !(x <= 5) {skip; skip; x = x + 1}⦄
