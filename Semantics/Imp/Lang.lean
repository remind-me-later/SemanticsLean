import Semantics.Maps

def State := TotalMap Int
def State.nil: State := TotalMap.default 0

notation "σ₀" => State.nil

#eval σ₀ "x"
#eval (σ₀⟪"x" ≔ 3⟫⟪"x" ≔ 4⟫) "x"
#eval (σ₀⟪"x" ≔ 3⟫⟪"x" ≔ 4⟫⟪"x" ≔ 7⟫) "x"

example: σ₀⟪"x" ≔ 3⟫ = σ₀⟪"x" ≔ 4⟫⟪"x" ≔ 3⟫ := TotalMap.clobber.symm

inductive Aexp where
  | val₁ : Int → Aexp
  | var₁ : String → Aexp
  -- arithmetic
  | add₁ : Aexp → Aexp → Aexp
  | sub₁ : Aexp → Aexp → Aexp
  | mul₁ : Aexp → Aexp → Aexp

-- x + 3
#check Aexp.add₁ (Aexp.var₁ "x") (Aexp.val₁ 3)

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

-- !(x <= 3)
#check Bexp.not₁ (Bexp.le₁ (Aexp.var₁ "x") (Aexp.val₁ 3))

inductive Com where
  | skip₁
  | cat₁   : Com → Com → Com
  | ass₁   : String → Aexp → Com
  | if₁    : Bexp → Com → Com → Com
  | while₁ : Bexp → Com → Com

/-
## Syntax
-/
-- Meta syntax
-- aexp
notation:60 a:55 " * " b:56 => Aexp.mul₁ a b
notation:60 a:60 " + " b:61 => Aexp.add₁ a b
notation:60 a:60 " - " b:61 => Aexp.sub₁ a b
-- bexp
notation:65 a:65 " && " b:66 => Bexp.and₁ a b
notation:65 a:65 " || " b:66 => Bexp.or₁ a b
notation:70 a:70 " == " b:71 => Bexp.eq₁ a b
notation:70 a:70 " <= " b:71 => Bexp.le₁ a b
notation:80 "!" a:81 => Bexp.not₁ a
-- com
notation a:40 ";;" b:41 => Com.cat₁ a b
notation:50 a:50 " = " b:51 => Com.ass₁ a b
notation "if " c " then " a " else " b "end" => Com.if₁ c a b
notation "while " c " loop " a "end" => Com.while₁ c a

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
syntax "if" imp "then" imp "else" imp " end" : imp
syntax "while" imp "loop" imp " end" : imp
-- meta
syntax "⦃" imp "⦄" : term

macro_rules
  -- keywords
  | `(⦃skip⦄) => `(Com.skip₁)
  | `(⦃true⦄) => `(Bexp.true₁)
  | `(⦃false⦄) => `(Bexp.false₁)
  -- general
  | `(⦃($x)⦄) => `(⦃$x⦄)
  -- aexp
  | `(⦃$x:ident⦄) => `(Aexp.var₁ $(Lean.quote (toString x.getId)))
  | `(⦃$n:num⦄)   => `(Aexp.val₁ $n)
  | `(⦃$x + $y⦄)  => `(Aexp.add₁ ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x - $y⦄)  => `(Aexp.sub₁ ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x * $y⦄)  => `(Aexp.mul₁ ⦃$x⦄ ⦃$y⦄)
  -- bexp
  | `(⦃!$x⦄)      => `(Bexp.not₁ ⦃$x⦄)
  | `(⦃$x && $y⦄)  => `(Bexp.and₁ ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x || $y⦄)  => `(Bexp.or₁ ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x == $y⦄)  => `(Bexp.eq₁ ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x <= $y⦄)  => `(Bexp.le₁ ⦃$x⦄ ⦃$y⦄)
  -- com
  | `(⦃$x:ident = $y⦄) => `(Com.ass₁ $(Lean.quote (toString x.getId)) ⦃$y⦄)
  | `(⦃$x ; $y⦄)       => `(Com.cat₁ ⦃$x⦄ ⦃$y⦄)
  | `(⦃if $b then $x else $y end⦄) => `(Com.if₁ ⦃$b⦄ ⦃$x⦄ ⦃$y⦄)
  | `(⦃while $b loop $x end⦄) => `(Com.while₁ ⦃$b⦄ ⦃$x⦄)

#check ⦃
  z = 4;
  if 3 <= 2 then
    y = 4 + 2
  else
    skip
  end
⦄

#check ⦃
  while true loop
    skip
  end
⦄

#check ⦃skip⦄

#check ⦃x = 5⦄

#check ⦃x = 5; y = 6⦄

#check ⦃
  if x <= 5 then
    y = 6
  else
    z = 7
  end
⦄

#check ⦃
  x = 0;
  while !(x <= 5) loop
    skip;
    skip;
    x = x + 1
  end
⦄
