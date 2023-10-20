inductive 𝔸 
  | num  : Int → 𝔸
  | loc  : String → 𝔸
  | sum  : 𝔸 → 𝔸 → 𝔸
  | prod : 𝔸 → 𝔸 → 𝔸

inductive 𝔹 
  | true  : 𝔹
  | false : 𝔹
  | eq    : 𝔸 → 𝔸 → 𝔹
  | le    : 𝔸 → 𝔸 → 𝔹
  | not   : 𝔹 → 𝔹
  | and   : 𝔹 → 𝔹 → 𝔹
  | or    : 𝔹 → 𝔹 → 𝔹

inductive ℂ 
  | skip  : ℂ
  | ass   : String → 𝔸 → ℂ
  | seq   : ℂ → ℂ → ℂ
  | cond  : 𝔹 → ℂ → ℂ → ℂ 
  | while : 𝔹 → ℂ → ℂ

-- Syntax of the language
declare_syntax_cat imp

-- general
syntax "(" imp ")" : imp
-- imp
syntax num : imp
syntax ident: imp
syntax:60 imp:60 "+" imp:61 : imp
syntax:70 imp:70 "*" imp:71 : imp
-- bexp
syntax:200 "tt" : imp
syntax:200 "ff" : imp
syntax:80 "!" imp:81 : imp
syntax:70 imp:70 "==" imp:71 : imp
syntax:70 imp:70 "<=" imp:71 : imp
syntax:65 imp:65 "||" imp:66 : imp
syntax:65 imp:65 "&&" imp:66 : imp
-- stmt
syntax "nop" : imp
syntax:50 imp:50 "=" imp:51 : imp
syntax:40 imp:40 ";" imp:41 : imp
syntax "if" imp "{" imp "}" "else" "{" imp "}" : imp
syntax "while" imp "{" imp "}" : imp

-- meta
syntax "⦃" imp "⦄" : term
syntax "." ident: imp

macro_rules
  -- general
  | `(⦃($x)⦄)     => `(⦃$x⦄)
  -- imp
  -- | `(⦃$s:str⦄)   => `(𝔸.loc $s)
  | `(⦃$x:ident⦄) => `(𝔸.loc $(Lean.quote (toString x.getId)))
  | `(⦃$n:num⦄)   => `(𝔸.num $n)
  | `(⦃$x + $y⦄)  => `(𝔸.sum ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x * $y⦄)  => `(𝔸.prod ⦃$x⦄ ⦃$y⦄)
  -- bexp
  | `(⦃tt⦄)        => `(𝔹.true)
  | `(⦃ff⦄)        => `(𝔹.false)
  | `(⦃!$x⦄)       => `(𝔹.not ⦃$x⦄)
  | `(⦃$x == $y⦄)  => `(𝔹.eq ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x <= $y⦄)  => `(𝔹.le ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x && $y⦄)  => `(𝔹.and ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x || $y⦄)  => `(𝔹.or ⦃$x⦄ ⦃$y⦄)
  -- stmt
  | `(⦃nop⦄)           => `(ℂ.skip)
  | `(⦃$x:ident = $y⦄) => `(ℂ.ass $(Lean.quote (toString x.getId)) ⦃$y⦄)
  | `(⦃$x ; $y⦄)       => `(ℂ.seq ⦃$x⦄ ⦃$y⦄)
  | `(⦃if $b {$x} else {$y}⦄) => `(ℂ.cond ⦃$b⦄ ⦃$x⦄ ⦃$y⦄)
  | `(⦃while $b {$x}⦄) => `(ℂ.while ⦃$b⦄ ⦃$x⦄)
  -- meta variables
  | `(⦃.$x:ident⦄) => `($x)
  | `(⦃.$x:ident = $y⦄) => `(ℂ.ass $x ⦃$y⦄)

#check ⦃z = 4; if 3 <= 2 {y = 4 + 2} else {nop}⦄
#check ⦃while tt {nop}⦄
#check ⦃nop⦄
#check ⦃x = 5⦄
#check ⦃x = 5; y = 6⦄
#check ⦃if x == 5 {y = 6} else {z = 7}⦄
#check ⦃x = 0; while !(x == 5) {nop; nop; x = x + 1}⦄
