inductive Aexp 
  | num  : Int → Aexp
  | loc  : String → Aexp
  | sum  : Aexp → Aexp → Aexp
  | prod : Aexp → Aexp → Aexp

inductive Bexp 
  | true  : Bexp
  | false : Bexp
  | eq    : Aexp → Aexp → Bexp
  | le    : Aexp → Aexp → Bexp
  | not   : Bexp → Bexp
  | and   : Bexp → Bexp → Bexp
  | or    : Bexp → Bexp → Bexp

inductive Com 
  | skipc  : Com
  | assc   : String → Aexp → Com
  | seqc   : Com → Com → Com
  | condc  : Bexp → Com → Com → Com 
  | whilec : Bexp → Com → Com

-- Meta syntax
notation "nᵢ" n => Aexp.num n
notation "lᵢ" x => Aexp.loc x
notation:60 a₁:60 " +ᵢ " a₂:61 => Aexp.sum a₁ a₂
notation:70 a₁:70 " *ᵢ " a₂:71 => Aexp.prod a₁ a₂

notation "trueᵢ" => Bexp.true
notation "falseᵢ" => Bexp.false
notation:80 "¬ᵢ" a:81 => Bexp.not a
notation:70 a₁:70 " =ᵢ " a₂:71 => Bexp.eq a₁ a₂
notation:70 a₁:70 " ≤ᵢ " a₂:71 => Bexp.le a₁ a₂
notation:65 b₁:65 " ∨ᵢ " b₂:66 => Bexp.or b₁ b₂
notation:65 b₁:65 " ∧ᵢ " b₂:66 => Bexp.and b₁ b₂

notation "skipᵢ" => Com.skipc
notation:50 c₁:50 " ≔ᵢ " c₂:51 => Com.assc c₁ c₂
notation:40 c₁:40 " ;ᵢ " c₂:41 => Com.seqc c₁ c₂
notation "ifᵢ " b " thenᵢ " c₁ " elseᵢ " c₂ " endᵢ" => Com.condc b c₁ c₂
notation "whileᵢ " b " doᵢ " c " endᵢ" => Com.whilec b c

-- Syntax of the language
declare_syntax_cat imp

-- general
syntax "(" imp ")" : imp
-- imp
syntax num : imp
syntax str : imp
syntax ident: imp
syntax:60 imp:60 "+" imp:61 : imp
syntax:70 imp:70 "*" imp:71 : imp
-- bexp
syntax "⊤" : imp
syntax "⊥" : imp
syntax:80 "¬" imp:81 : imp
syntax:70 imp:70 "=" imp:71 : imp
syntax:70 imp:70 "≤" imp:71 : imp
syntax:65 imp:65 "∨" imp:66 : imp
syntax:65 imp:65 "∧" imp:66 : imp
-- stmt
syntax "nop" : imp
syntax:50 imp:50 "≔" imp:51 : imp
syntax:40 imp:40 ";" imp:41 : imp
syntax "if" imp "then" imp "else" imp "end" : imp
syntax "while" imp "do" imp "end" : imp

syntax "⦃" imp "⦄" : term

macro_rules
  -- general
  | `(⦃($x)⦄) => `(⦃$x⦄)
  -- imp
  | `(⦃$s:str⦄) => `(lᵢ $s)
  | `(⦃$x:ident⦄) => `(lᵢ $(Lean.quote (toString x.getId)))
  | `(⦃$n:num⦄) => `(nᵢ $n)
  | `(⦃$x + $y⦄) => `(⦃$x⦄ +ᵢ ⦃$y⦄)
  | `(⦃$x * $y⦄) => `(⦃$x⦄ *ᵢ ⦃$y⦄)
  -- bexp
  | `(⦃⊤⦄) => `(trueᵢ)
  | `(⦃⊥⦄) => `(falseᵢ)
  | `(⦃¬$x⦄) => `(¬ᵢ⦃$x⦄)
  | `(⦃$x = $y⦄) => `(⦃$x⦄ =ᵢ ⦃$y⦄)
  | `(⦃$x ≤ $y⦄) => `(⦃$x⦄ ≤ᵢ ⦃$y⦄)
  | `(⦃$x ∧ $y⦄) => `(⦃$x⦄ ∧ᵢ ⦃$y⦄)
  | `(⦃$x ∨ $y⦄) => `(⦃$x⦄ ∨ᵢ ⦃$y⦄)
  -- stmt
  | `(⦃nop⦄) => `(skipᵢ)
  | `(⦃$x:ident ≔ $y⦄) => `($(Lean.quote (toString x.getId)) ≔ᵢ ⦃$y⦄)
  | `(⦃$x ; $y⦄) => `(⦃$x⦄ ;ᵢ ⦃$y⦄)
  | `(⦃if $x then $y else $z end⦄) => `(ifᵢ ⦃$x⦄ thenᵢ ⦃$y⦄ elseᵢ ⦃$z⦄ endᵢ)
  | `(⦃while $x do $y end⦄) => `(whileᵢ ⦃$x⦄ doᵢ ⦃$y⦄ endᵢ)

#check ⦃z ≔ 4; if 3 ≤ 2 then y ≔ 4 + 2 else nop end⦄
#check ⦃while ⊤ do nop end⦄
#check ⦃nop⦄
#check ⦃x ≔ 5⦄
#check ⦃x ≔ 5; y ≔ 6⦄
#check ⦃if x = 5 then y ≔ 6 else z ≔ 7 end⦄
#check ⦃x ≔ 0 ; while ¬(x = 5) do nop; nop; x ≔ x + 1 end⦄
