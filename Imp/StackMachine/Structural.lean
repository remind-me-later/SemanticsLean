import Imp.StackMachine.Syntax
import Mathlib.Data.List.Defs

inductive Instr.Step: Instr × StackMachine → StackMachine → Prop where
  | loadi₁:
    Step (loadi n, ⟨pc, s, stk⟩) ⟨pc + 1, s, n::stk⟩

  | load₁:
    Step (load x, ⟨pc, s, stk⟩) ⟨pc + 1, s, (s x)::stk⟩

  | add₁ (h: a::b::t = stk):
    Step (add, ⟨pc, s, stk⟩) ⟨pc + 1, s, (a + b)::t⟩

  | store₁ (h: a::t = stk):
    Step (store x, ⟨pc, s, stk⟩) ⟨pc + 1, s⟪x ≔ a⟫, t⟩

  | jmp₁:
    Step (jmp n, ⟨pc, s, stk⟩) ⟨pc + 1 + n, s, stk⟩

  | jmplt₁ (h: a::b::t = stk):
    Step (jmplt n, ⟨pc, s, stk⟩) ⟨bif b < a then pc + 1 + n else pc + 1, s, stk⟩

  | jmpge₁ (h: a::b::t = stk):
    Step (jmpge n, ⟨pc, s, stk⟩) ⟨bif b ≥ a then pc + 1 + n else pc + 1, s, stk⟩
