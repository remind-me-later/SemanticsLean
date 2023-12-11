inductive Ty where
  | Bool
  | Arrow: Ty → Ty → Ty

inductive Term where
  | var: String → Term
  | app: Term → Term → Term
  | abs: String → Ty → Term → Term
  | true
  | false
  | cond: Term → Term → Term → Term

-- Syntax of the language
declare_syntax_cat stlc

syntax "(" stlc ")" : stlc
syntax ident: stlc
-- stmt
syntax "λ" ident ":" stlc "↦" stlc : stlc
syntax "if " stlc " then " stlc " else " stlc : stlc
syntax stlc " → " stlc : stlc
syntax stlc stlc : stlc
-- meta
syntax "⦃" stlc "⦄" : term

macro_rules
  -- keywords
  | `(⦃true⦄)   => `(Term.true)
  | `(⦃false⦄)  => `(Term.false)
  | `(⦃Bool⦄)   => `(Ty.Bool)
  | `(⦃$x → $y⦄) => `(Ty.Arrow ⦃$x⦄ ⦃$y⦄)
  -- general
  | `(⦃($x)⦄) => `(⦃$x⦄)
  | `(⦃$x:ident⦄) => `(Term.var $(Lean.quote (toString x.getId)))
  -- stlc
  | `(⦃λ $x : $t ↦ $e⦄) => `(Term.abs $(Lean.quote (toString x.getId)) ⦃$t⦄ ⦃$e⦄)
  | `(⦃$x $y⦄) => `(Term.app ⦃$x⦄ ⦃$y⦄)
  | `(⦃if $b then $x else $y⦄) => `(Term.cond ⦃$b⦄ ⦃$x⦄ ⦃$y⦄)


#check ⦃(λx:Bool↦x) true⦄
#check ⦃(λx:Bool↦if x then false else true) true⦄
#check ⦃λf:Bool→Bool↦f (f true)⦄
