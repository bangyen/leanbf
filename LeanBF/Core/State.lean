/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Instruction
import Mathlib.Data.Int.Basic

/-!
# The Machine State

## Main definitions

* `State`: The state of the Brainfuck machine.
* `State.mkEmpty`: The initial state.
* `State.modifyCell`: Apply a function to the cell at the pointer.
* `State.incVal`: Increment the current cell (`+`).
* `State.decVal`: Decrement the current cell (`-`).
* `State.incPtr`: Move the pointer right (`>`).
* `State.decPtr`: Move the pointer left (`<`).
* `State.currentVal`: The value of the current cell.
-/

namespace LeanBF

/-- The state of the Brainfuck machine -/
structure State where
  /-- The pointer location on the tape. -/
  ptr : Int
  /-- The infinite tape mapping cell indices to values. -/
  tape : Int → Nat
  /-- The remaining input stream. -/
  input : List Nat
  /-- The output stream produced so far. -/
  output : List Nat
  deriving Inhabited

namespace State

/-- The initial state: pointer at cell `0`, all cells zero, empty I/O. -/
def mkEmpty : State where
  ptr  := 0
  tape := fun _ ↦ 0
  input  := []
  output := []

/-- Modify the cell at the current pointer -/
def modifyCell (s : State) (f : Nat → Nat) : State :=
  { s with tape := fun i ↦ if i = s.ptr then f (s.tape i) else s.tape i }

/-- Increment the current cell (`+`). -/
def incVal (s : State) : State := s.modifyCell (· + 1)

/-- Decrement the current cell (`-`). -/
def decVal (s : State) : State := s.modifyCell (· - 1)

/-- Move the pointer right (`>`). -/
def incPtr (s : State) : State := { s with ptr := s.ptr + 1 }

/-- Move the pointer left (`<`). -/
def decPtr (s : State) : State := { s with ptr := s.ptr - 1 }

/-- The value of the cell at the current pointer. -/
def currentVal (s : State) : Nat := s.tape s.ptr

end State

end LeanBF
