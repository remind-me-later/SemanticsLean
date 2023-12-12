inductive Ty where
  | Bool
  | Arrow: Ty → Ty → Ty

inductive Term where
  | var: String → Term
  | app: Term → Term → Term
  | abs: String → Ty → Term → Term
  | tt
  | ff
  | cond: Term → Term → Term → Term



-- Syntax of the language
declare_syntax_cat stlc

syntax "(" stlc ")" : stlc
syntax ident: stlc
-- stmt
syntax "Λ" ident ":" stlc "↦" stlc : stlc
syntax stlc "?" stlc "|" stlc : stlc
syntax stlc " → " stlc : stlc
syntax stlc ".." stlc : stlc
syntax "⊤": stlc
syntax "⊥": stlc
syntax "𝔹": stlc

-- meta
syntax "⦃" stlc "⦄" : term

macro_rules
  -- keywords
  | `(⦃⊤⦄)   => `(Term.tt)
  | `(⦃⊥⦄)  => `(Term.ff)
  | `(⦃𝔹⦄)   => `(Ty.Bool)
  | `(⦃$x → $y⦄) => `(Ty.Arrow ⦃$x⦄ ⦃$y⦄)
  -- general
  | `(⦃($x)⦄) => `(⦃$x⦄)
  | `(⦃$x:ident⦄) => `(Term.var $(Lean.quote (toString x.getId)))
  -- stlc
  | `(⦃Λ $x : $t ↦ $e⦄) => `(Term.abs $(Lean.quote (toString x.getId)) ⦃$t⦄ ⦃$e⦄)
  | `(⦃$x..$y⦄) => `(Term.app ⦃$x⦄ ⦃$y⦄)
  | `(⦃$b ? $x | $y⦄) => `(Term.cond ⦃$b⦄ ⦃$x⦄ ⦃$y⦄)


#check ⦃(Λ x: 𝔹 ↦x)..⊤⦄
#check ⦃(Λ x: 𝔹 ↦ x ? ⊥ | ⊤)..⊤⦄
#check ⦃Λ f: 𝔹 → 𝔹 ↦ f..(f..⊤)⦄

notation "Λ " x ": " T " ↦ " t => Term.abs x T t
infix:100 ".." => Term.app
notation b " ? " a " | " c => Term.cond b a c
notation "⊤" => Term.tt
notation "⊥" => Term.ff
infix:100 "→" => Ty.Arrow
notation "𝔹" => Ty.Bool
