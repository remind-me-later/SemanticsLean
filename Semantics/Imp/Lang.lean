import Semantics.Maps

def State := Map Int
def s0: State := Map.default 0

#eval s0 "x"
#eval (s0["x" ← 3]["x" ← 4]) "x"
#eval (s0["x" ← 3]["x" ← 4]["x" ← 7]) "x" -- 7

example: s0["x" ← 3] = s0["x" ← 4]["x" ← 3] := Map.forget.symm

inductive Aexp where
  | val : Int → Aexp
  | var : String → Aexp
  -- arithmetic
  | add : Aexp → Aexp → Aexp
  | sub : Aexp → Aexp → Aexp
  | mul : Aexp → Aexp → Aexp

instance: OfNat Aexp n := ⟨.val n⟩
instance: Add Aexp := ⟨.add⟩
instance: Sub Aexp := ⟨.sub⟩
instance: Neg Aexp := ⟨(.sub 0 .)⟩
instance: Mul Aexp := ⟨.mul⟩

-- x + 3
#check Aexp.var "x" + 3

-- x * -3
#check Aexp.var "x" * -3

inductive Bexp where
  -- constants
  | true
  | false
  -- boolean
  | not : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or  : Bexp → Bexp → Bexp
  -- comparison
  | eq : Aexp → Aexp → Bexp
  | le : Aexp → Aexp → Bexp

instance: Complement Bexp := ⟨.not⟩
instance: AndOp Bexp := ⟨.and⟩
instance: OrOp Bexp := ⟨.or⟩

-- !(x <= 3)
#check ~~~(Bexp.le (Aexp.var "x") 3)

inductive Com where
  | skip
  | cat       : Com → Com → Com
  | ass       : String → Aexp → Com
  | ifElse    : Bexp → Com → Com → Com
  | whileLoop : Bexp → Com → Com

instance: EmptyCollection Com := ⟨.skip⟩
instance: Append Com := ⟨.cat⟩

-- ## Syntax

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
syntax "[|" imp "|]" : term

macro_rules
-- keywords
| `([|skip|]) => `(Com.skip)
| `([|true|]) => `(Bexp.true)
| `([|false|]) => `(Bex.false)
-- general
| `([|($x)|]) => `([|$x|])
-- aexp
| `([|$x:ident|]) => `(Aexp.var $(Lean.quote x.getId.toString))
| `([|$n:num|])   => `($n)
| `([|$x + $y|])  => `([|$x|] + [|$y|])
| `([|$x - $y|])  => `([|$x|] - [|$y|])
| `([|$x * $y|])  => `([|$x|] * [|$y|])
-- bexp
| `([|!$x|])      => `(~~~[|$x|])
| `([|$x && $y|]) => `([|$x|] &&& [|$y|])
| `([|$x || $y|]) => `([|$x|] ||| [|$y|])
| `([|$x == $y|]) => `(Bexp.eq [|$x|] [|$y|])
| `([|$x <= $y|]) => `(Bexp.le [|$x|] [|$y|])
-- com
| `([|$x:ident = $y|]) => `(Com.ass $(Lean.quote x.getId.toString) [|$y|])
| `([|$x ; $y|])       => `(Com.cat [|$x|] [|$y|])
| `([|if $b {$x} else {$y}|]) => `(Com.ifElse [|$b|] [|$x|] [|$y|])
| `([|while $b {$x}|]) => `(Com.whileLoop [|$b|] [|$x|])

#check [|
  n = 5; i = 2; res = 1;

  while i <= n {
      res = res * i;
      i = i + 1
  }
|]
