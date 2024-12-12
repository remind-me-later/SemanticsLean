import Semantics.Maps

def State := Map Int
def s0: State := Map.default 0

#eval s0 "x"
#eval (s0["x" <- 3]["x" <- 4]) "x"
#eval (s0["x" <- 3]["x" <- 4]["x" <- 7]) "x" -- 7

example: s0["x" <- 3] = s0["x" <- 4]["x" <- 3] := Map.forget.symm

inductive Aexp where
  | val : Int -> Aexp
  | var : String -> Aexp
  -- arithmetic
  | add : Aexp -> Aexp -> Aexp
  | sub : Aexp -> Aexp -> Aexp
  | mul : Aexp -> Aexp -> Aexp

instance: OfNat Aexp n := OfNat.mk $ Aexp.val n
instance: Add Aexp := Add.mk Aexp.add
instance: Sub Aexp := Sub.mk Aexp.sub
instance: Neg Aexp := Neg.mk (Aexp.sub 0 .)
instance: Mul Aexp := Mul.mk Aexp.mul

-- x + 3
#check Aexp.var "x" + 3

-- x * -3
#check Aexp.var "x" * -3

inductive Bexp where
  -- constants
  | true
  | false
  -- boolean
  | not : Bexp -> Bexp
  | and : Bexp -> Bexp -> Bexp
  | or  : Bexp -> Bexp -> Bexp
  -- comparison
  | eq : Aexp -> Aexp -> Bexp
  | le : Aexp -> Aexp -> Bexp

instance: Complement Bexp := Complement.mk Bexp.not
instance: AndOp Bexp := AndOp.mk Bexp.and
instance: OrOp Bexp := OrOp.mk Bexp.or

-- !(x <= 3)
#check ~~~(Bexp.le (Aexp.var "x") 3)

inductive Com where
  | skip
  | cat        : Com -> Com -> Com
  | ass        : String -> Aexp -> Com
  | ifelse     : Bexp -> Com -> Com -> Com
  | whileloop  : Bexp -> Com -> Com

instance: Append Com := Append.mk Com.cat

/-
## Syntax
-/
-- Meta syntax
notation "if " c " then " a " else " b " end" => Com.ifelse c a b
notation "while " c " loop " a " end" => Com.whileloop c a

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
syntax:70 imp:70 "=" imp:71 : imp
syntax:70 imp:70 "<=" imp:71 : imp
syntax:80 "!" imp:81 : imp
-- com
syntax:40 imp:40 ";" imp:41 : imp
syntax:50 imp:50 ":=" imp:51 : imp
syntax "if" imp "then" imp "else" imp "end" : imp
syntax "while" imp "loop" imp "end" : imp
-- meta
syntax "[|" imp "|]" : term

macro_rules
  -- keywords
  | `([|skip|]) => `(Com.skip)
  | `([|true|]) => `(Bexp.true)
  | `([|false|]) => `(Bexp.false)
  -- general
  | `([|($x)|]) => `([|$x|])
  -- aexp
  | `([|$x:ident|]) => `(Aexp.var $(Lean.quote (toString x.getId)))
  | `([|$n:num|])   => `($n)
  | `([|$x + $y|])  => `([|$x|] + [|$y|])
  | `([|$x - $y|])  => `([|$x|] - [|$y|])
  | `([|$x * $y|])  => `([|$x|] * [|$y|])
  -- bexp
  | `([|!$x|])      => `(~~~[|$x|])
  | `([|$x && $y|]) => `([|$x|] &&& [|$y|])
  | `([|$x || $y|]) => `([|$x|] ||| [|$y|])
  | `([|$x = $y|]) => `(Bexp.eq [|$x|] [|$y|])
  | `([|$x <= $y|]) => `(Bexp.le [|$x|] [|$y|])
  -- com
  | `([|$x:ident := $y|]) => `(Com.ass $(Lean.quote (toString x.getId)) [|$y|])
  | `([|$x ; $y|])       => `(Com.cat [|$x|] [|$y|])
  | `([|if $b then $x else $y end|]) => `(Com.ifelse [|$b|] [|$x|] [|$y|])
  | `([|while $b loop $x end|]) => `(Com.whileloop [|$b|] [|$x|])

#check [|
n := 5; i := 2; res := 1;

while i <= n loop
    res := res * i;
    i := i + 1
end
|]
