inductive 𝔸
  | num : Int → 𝔸
  | loc : String → 𝔸
  | add : 𝔸 → 𝔸 → 𝔸
  | mul : 𝔸 → 𝔸 → 𝔸

inductive 𝔹
  | tt  : 𝔹
  | ff  : 𝔹
  | not : 𝔹 → 𝔹
  | and : 𝔹 → 𝔹 → 𝔹
  | or  : 𝔹 → 𝔹 → 𝔹
  | eq  : 𝔸 → 𝔸 → 𝔹
  | le  : 𝔸 → 𝔸 → 𝔹

inductive ℂ
  | skip  : ℂ
  | ass   : String → 𝔸 → ℂ
  | cat   : ℂ → ℂ → ℂ
  | ite   : 𝔹 → ℂ → ℂ → ℂ
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
syntax:80 "¬" imp:81 : imp
syntax:70 imp:70 "=" imp:71 : imp
syntax:70 imp:70 "≤" imp:71 : imp
syntax:65 imp:65 "∨" imp:66 : imp
syntax:65 imp:65 "∧" imp:66 : imp
-- stmt
syntax:50 imp:50 "≔" imp:51 : imp
syntax:40 imp:40 ";" imp:41 : imp
syntax "if" imp "{" imp "}" "else" "{" imp "}" : imp
syntax "while" imp "{" imp "}" : imp

-- meta
syntax "⦃" imp "⦄" : term
syntax "⟪" imp "⟫" : term

macro_rules
  -- keywords
  | `(⦃skip⦄) => `(ℂ.skip)
  | `(⦃tt⦄)   => `(𝔹.tt)
  | `(⦃ff⦄)   => `(𝔹.ff)
  -- general
  | `(⦃($x)⦄) => `(⦃$x⦄)
  -- imp
  | `(⦃$n:num⦄)   => `(𝔸.num $n)
  | `(⦃$x + $y⦄)  => `(𝔸.add ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x * $y⦄)  => `(𝔸.mul ⦃$x⦄ ⦃$y⦄)
  -- bexp
  | `(⦃¬$x⦄)      => `(𝔹.not ⦃$x⦄)
  | `(⦃$x = $y⦄)  => `(𝔹.eq ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x ≤ $y⦄)  => `(𝔹.le ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x ∧ $y⦄)  => `(𝔹.and ⦃$x⦄ ⦃$y⦄)
  | `(⦃$x ∨ $y⦄)  => `(𝔹.or ⦃$x⦄ ⦃$y⦄)
  -- stmt
  | `(⦃$x ; $y⦄)       => `(ℂ.cat ⦃$x⦄ ⦃$y⦄)
  | `(⦃if $b {$x} else {$y}⦄) => `(ℂ.ite ⦃$b⦄ ⦃$x⦄ ⦃$y⦄)
  | `(⦃while $b {$x}⦄) => `(ℂ.while ⦃$b⦄ ⦃$x⦄)
  -- meta variables
  | `(⦃$x:ident⦄) => `($x)
  | `(⦃$x:ident ≔ $y⦄) => `(ℂ.ass $x ⦃$y⦄)

macro_rules
  -- keywords
  | `(⟪skip⟫) => `(ℂ.skip)
  | `(⟪tt⟫)   => `(𝔹.tt)
  | `(⟪ff⟫)   => `(𝔹.ff)
  -- general
  | `(⟪($x)⟫) => `(⟪$x⟫)
  -- imp
  | `(⟪$x:ident⟫) => `(𝔸.loc $(Lean.quote (toString x.getId)))
  | `(⟪$n:num⟫)   => `(𝔸.num $n)
  | `(⟪$x + $y⟫)  => `(𝔸.add ⟪$x⟫ ⟪$y⟫)
  | `(⟪$x * $y⟫)  => `(𝔸.mul ⟪$x⟫ ⟪$y⟫)
  -- bexp
  | `(⟪¬$x⟫)       => `(𝔹.not ⟪$x⟫)
  | `(⟪$x = $y⟫)  => `(𝔹.eq ⟪$x⟫ ⟪$y⟫)
  | `(⟪$x ≤ $y⟫)  => `(𝔹.le ⟪$x⟫ ⟪$y⟫)
  | `(⟪$x ∧ $y⟫)  => `(𝔹.and ⟪$x⟫ ⟪$y⟫)
  | `(⟪$x ∨ $y⟫)  => `(𝔹.or ⟪$x⟫ ⟪$y⟫)
  -- stmt
  | `(⟪$x:ident ≔ $y⟫) => `(ℂ.ass $(Lean.quote (toString x.getId)) ⟪$y⟫)
  | `(⟪$x ; $y⟫)       => `(ℂ.cat ⟪$x⟫ ⟪$y⟫)
  | `(⟪if $b {$x} else {$y}⟫) => `(ℂ.ite ⟪$b⟫ ⟪$x⟫ ⟪$y⟫)
  | `(⟪while $b {$x}⟫) => `(ℂ.while ⟪$b⟫ ⟪$x⟫)

#check ⟪z ≔ 4; if 3 ≤ 2 {y ≔ 4 + 2} else {skip}⟫
#check ⟪while tt {skip}⟫
#check ⟪skip⟫
#check ⟪x ≔ 5⟫
#check ⟪x ≔ 5; y ≔ 6⟫
#check ⟪if x = 5 {y ≔ 6} else {z ≔ 7}⟫
#check ⟪x ≔ 0; while ¬(x = 5) {skip; skip; x ≔ x + 1}⟫
