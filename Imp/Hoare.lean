import Imp.Natural

def 𝕊.assert := 𝕊 → Prop

def 𝕊.assert.implies (P Q: assert): Prop := ∀s, P s → Q s

notation P "->>" Q => 𝕊.assert.implies P Q
notation P "<<->>" Q => 𝕊.assert.implies P Q ∧ 𝕊.assert.implies Q P
