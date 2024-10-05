import Semantics.Maps

def State := TotalMap Int
def s₀: State := TotalMap.default 0

#eval s₀ "x"
#eval (s₀["x" ← 3]["x" ← 4]) "x"
#eval (s₀["x" ← 3]["x" ← 4]["x" ← 7]) "x"

example: s₀["x" ← 3] = s₀["x" ← 4]["x" ← 3] := TotalMap.clobber.symm

inductive Aexp where
  | val₁ : Int → Aexp
  | var₁ : String → Aexp
  -- arithmetic
  | add₁ : Aexp → Aexp → Aexp
  | sub₁ : Aexp → Aexp → Aexp
  | mul₁ : Aexp → Aexp → Aexp

instance: OfNat Aexp n := ⟨Aexp.val₁ n⟩
instance: Coe String Aexp := ⟨Aexp.var₁⟩
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
#check ~~~(Bexp.le₁ "x" 3)

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
  | `(⦃$n:num⦄)   => `($n)
  | `(⦃$x + $y⦄)  => `(⦃$x⦄ + ⦃$y⦄)
  | `(⦃$x - $y⦄)  => `(⦃$x⦄ - ⦃$y⦄)
  | `(⦃$x * $y⦄)  => `(⦃$x⦄ * ⦃$y⦄)
  -- bexp
  | `(⦃!$x⦄)      => `(~~~⦃$x⦄)
  | `(⦃$x && $y⦄) => `(⦃$x⦄ &&& ⦃$y⦄)
  | `(⦃$x || $y⦄) => `(⦃$x⦄ ||| ⦃$y⦄)
  | `(⦃$x == $y⦄) => `(Bexp.eq₁ ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x <= $y⦄) => `(Bexp.le₁ ⦃$x⦄ ⦃$y⦄)
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