import Imp.StackMachine.Syntax
import Mathlib.Data.List.Defs

inductive Instr.Step: Instr × StackMachine → StackMachine → Prop where
  | loadi₁:
    Step (loadi n, ⟨pc, s, stk⟩) ⟨pc + 1, s, stk.concat n⟩

  | load₁:
    Step (load x, ⟨pc, s, stk⟩) ⟨pc + 1, s, stk.concat $ s x⟩

  | add₁:
    Step (add, ⟨pc, s, stk⟩) ⟨pc + 1, s, stk.concat (stk.take 2).sum⟩

  | store₁:
    Step (store x, ⟨pc, s, stk⟩) ⟨pc + 1, s⟪x ≔ stk.headD 0⟫, stk.tail⟩

  | jmp₁:
    Step (jmp n, ⟨pc, s, stk⟩) ⟨pc + 1 + n, s, stk⟩

  | jmplt₁:
    Step (jmplt n, ⟨pc, s, stk⟩) ⟨bif stk.tail.headD 0 < stk.headD 0 then pc + 1 + n else pc + 1, s, stk⟩

  | jmpge₁:
    Step (jmpge n, ⟨pc, s, stk⟩) ⟨bif stk.tail.headD 0 ≥ stk.headD 0 then pc + 1 + n else pc + 1, s, stk⟩
