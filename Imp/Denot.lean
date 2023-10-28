import Imp.State
import Imp.Aexp
import Imp.Bexp
import Imp.Syntax

import Mathlib.Init.Classical




def Γ (t: 𝕊 → Bool) (f: 𝕊 → Option 𝕊) (g: 𝕊 → Option 𝕊): 𝕊 → Option 𝕊 :=
  fun σ => ite (t σ) (f σ >>= g) σ

theorem ℂ.fix t f: ∃g, Γ t f g = g :=
  by sorry


noncomputable def ℂ.ρ (c: ℂ) (σ: 𝕊): Option 𝕊 :=
  match c with
  | skip   => σ
  | x ≔ₛ a => 𝕊.update σ x (𝔸.ρ a σ)
  | c₁;ₛc₂ => ρ c₁ σ >>= ρ c₂
  | ife b c₁ c₂ => ite (𝔹.ρ b σ) (ρ c₁ σ) (ρ c₂ σ)
  | wle b c => Classical.choose (fix (𝔹.ρ b) (ρ c)) σ
