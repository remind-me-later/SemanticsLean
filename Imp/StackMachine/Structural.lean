import Imp.StackMachine.Syntax
import Mathlib.Data.List.Defs

inductive Instr.Step: Instr × StackMachine → StackMachine → Prop where
  | loadi₁:
    Step (loadi n, ⟨pc, s, stk⟩) ⟨pc + 1, s, stk.concat n⟩

  | load₁:
    Step (load x, ⟨pc, s, stk⟩) ⟨pc + 1, s, stk.concat $ s x⟩

  | add₁ (h: [a, b] = stk.take 2):
    Step (add, ⟨pc, s, stk⟩) ⟨pc + 1, s, stk.tail.tail.concat $ a + b⟩

  | store₁ (h: some head = stk.head?):
    Step (store x, ⟨pc, s, stk⟩) ⟨pc + 1, s⟪x ≔ head⟫, stk.tail⟩

  | jmp₁:
    Step (jmp n, ⟨pc, s, stk⟩) ⟨pc + 1 + n, s, stk⟩

  | jmplt₁ (h: [a, b] = stk.take 2):
    Step (jmplt n, ⟨pc, s, stk⟩) ⟨bif b < a then pc + 1 + n else pc + 1, s, stk⟩

  | jmpge₁ (h: [a, b] = stk.take 2):
    Step (jmpge n, ⟨pc, s, stk⟩) ⟨bif b ≥ a then pc + 1 + n else pc + 1, s, stk⟩
