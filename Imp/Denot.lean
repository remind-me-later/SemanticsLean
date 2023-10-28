import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

import Mathlib.Init.Classical




def Γ (t: Σ → Bool) (f: Σ → Option Σ) (g: Σ → Option Σ): Σ → Option Σ :=
  fun σ => ite (t σ = true) (f σ >>= g) σ

theorem ℂ.fix t f: ∃g, Γ t f g = g :=
  by sorry


noncomputable def ℂ.ev (c: ℂ) (σ: Σ): Option Σ :=
  match c with
  | ⦃nop⦄     => σ
  | ⦃.x = .a⦄ => State.update σ x ⟪a, σ⟫
  | ⦃.c₁;.c₂⦄ => ℂ.ev c₁ σ >>= ℂ.ev c₂
  | ⦃if .b {.c₁} else {.c₂}⦄ => ite (⟪b, σ⟫ = true) (ℂ.ev c₁ σ) (ℂ.ev c₂ σ)
  | ⦃while .b {.c}⦄ => Classical.choose (ℂ.fix (𝔹.ev b) (ℂ.ev c)) σ
