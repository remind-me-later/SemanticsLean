import Imp.State

inductive Instr where
  | loadi : Int → Instr
  | load  : String → Instr
  | add   : Instr
  | store : String → Instr
  | jmp   : Int → Instr
  | jmplt : Int → Instr
  | jmpge : Int → Instr

structure StackMachine where
  pc    : Int
  state : State
  stack : List Int
