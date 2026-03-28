import Mathlib.Data.Int.Basic

/-- Brainfuck instructions -/
inductive Instruction where
  | inc_ptr : Instruction  -- `>`
  | dec_ptr : Instruction  -- `<`
  | inc_val : Instruction  -- `+`
  | dec_val : Instruction  -- `-`
  | loop    : List Instruction → Instruction -- `[` and `]`
  | read    : Instruction  -- `,`
  | write   : Instruction  -- `.`
  deriving Repr, BEq

/-- A Brainfuck program is a list of instructions -/
abbrev Program := List Instruction

/-- The state of the Brainfuck machine -/
structure State where
  ptr : Int
  tape : Int → Nat
  input : List Nat
  output : List Nat
  deriving Inhabited

namespace State

def mkEmpty : State where
  ptr  := 0
  tape := fun _ ↦ 0
  input  := []
  output := []

/-- Modify the cell at the current pointer -/
def modifyCell (s : State) (f : Nat → Nat) : State :=
  { s with tape := fun i ↦ if i = s.ptr then f (s.tape i) else s.tape i }

def incVal (s : State) : State := s.modifyCell (· + 1)
def decVal (s : State) : State := s.modifyCell (· - 1)

def incPtr (s : State) : State := { s with ptr := s.ptr + 1 }
def decPtr (s : State) : State := { s with ptr := s.ptr - 1 }

def currentVal (s : State) : Nat := s.tape s.ptr

end State
