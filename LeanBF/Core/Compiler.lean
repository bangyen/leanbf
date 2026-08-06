/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Instruction
import LeanBF.Core.Minsky
import LeanBF.Core.State

/-!
# The Minsky-to-Brainfuck Compiler

## Main definitions

* `Compiler.movePtr`: Brainfuck code that moves the pointer between two cells.
* `Compiler.clearHere`: Clear the current cell to `0`.
* `Compiler.setHere`: Set the current cell to a constant.
* `Compiler.ifZeroElse`: Conditional on the current cell being zero.
* `Compiler.compileInstr`: The translation of a single Minsky instruction.
* `Compiler.compileProgram`: The full dispatch-loop program for a Minsky program.

The compiled program keeps the pointer in the cell it addresses, so every
block starts and ends at a known cell. The layout is: cell 0 is the `running`
flag, cell 1 holds the program counter `pc`, cells 2 and 3 hold `c1` and
`c2`, cell 4 is the `done` flag used by the dispatcher, and the scratch cells
5-16 back the three `ifZeroElse` layers (the `done` test, the `pc` test, and
the counter test inside `jzdec`).

`ifZeroElse test thenBody elseBody` preserves the tested cell, runs
`thenBody` exactly once when the cell is `0` and `elseBody` exactly once
otherwise, and restores all scratch cells to `0`. Both bodies must start and
end with the pointer on the tested cell.
-/

namespace LeanBF

namespace Compiler

/-- Move the pointer from cell `i` to cell `j`. -/
def movePtr (i j : Int) : Program :=
  if i < j then
    List.replicate (j - i).toNat .inc_ptr
  else
    List.replicate (i - j).toNat .dec_ptr

/-- Clear the current cell to `0` (the pointer does not move). -/
def clearHere : Program :=
  [.loop [.dec_val]]

/-- Set the current cell to the constant `n` (the pointer does not move). -/
def setHere (n : ℕ) : Program :=
  clearHere ++ List.replicate n .inc_val

/--
Conditional on the current cell (the `test` cell) being `0`: run `thenBody`
when it is `0` and `elseBody` otherwise, each exactly once, and preserve the
tested cell. The four scratch cells `s1 s2 s3 s4` are cleared at the start
and restored to `0` at the end. Both bodies must start and end with the
pointer on the `test` cell.
-/
def ifZeroElse (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program) : Program :=
  movePtr test s1 ++ clearHere ++
  movePtr s1 s2 ++ clearHere ++
  movePtr s2 s3 ++ clearHere ++
  movePtr s3 s4 ++ clearHere ++
  movePtr s4 test ++
  -- copy the tested cell into s1, s2, and s4, zeroing it:
  [.loop (
    [.dec_val] ++
    movePtr test s1 ++ [.inc_val] ++
    movePtr s1 s2 ++ [.inc_val] ++
    movePtr s2 s4 ++ [.inc_val] ++
    movePtr s4 test
  )] ++
  -- s3 := 1, then clear s3 once per unit of s1: s3 = 1 iff the cell was 0:
  movePtr test s3 ++ [.inc_val] ++
  movePtr s3 s1 ++
  [.loop (
    [.dec_val] ++
    movePtr s1 s3 ++ [.dec_val] ++
    movePtr s3 s1
  )] ++
  movePtr s1 test ++
  -- restore the tested cell from s4:
  movePtr test s4 ++
  [.loop (
    [.dec_val] ++
    movePtr s4 test ++ [.inc_val] ++
    movePtr test s4
  )] ++
  movePtr s4 test ++
  -- else-body iff s2 is non-zero:
  movePtr test s2 ++
  [.loop (
    movePtr s2 test ++ elseBody ++
    movePtr test s2 ++ clearHere
  )] ++
  movePtr s2 test ++
  -- then-body iff s3 is non-zero (the cell was zero):
  movePtr test s3 ++
  [.loop (
    movePtr s3 test ++ thenBody ++
    movePtr test s3 ++ clearHere
  )] ++
  movePtr s3 test

/--
Compile a single Minsky instruction into a Brainfuck block. The block is part
of a dispatch loop: it starts and ends with the pointer on the `pc` cell (1).
A `jzdec` tests its counter with `ifZeroElse`, which preserves the counter
value, so the decrement branch works on the preserved value.
-/
def compileInstr (instr : Minsky.Instruction) : Program :=
  match instr with
  | .inc1 next =>
    movePtr 1 2 ++ [.inc_val] ++
    movePtr 2 1 ++
    setHere next
  | .inc2 next =>
    movePtr 1 3 ++ [.inc_val] ++
    movePtr 3 1 ++
    setHere next
  | .jzdec1 ifZero ifNonZero =>
    movePtr 1 2 ++
    ifZeroElse 2 13 14 15 16
      (movePtr 2 1 ++ setHere ifZero ++ movePtr 1 2)
      ([.dec_val] ++ movePtr 2 1 ++ setHere ifNonZero ++ movePtr 1 2) ++
    movePtr 2 1
  | .jzdec2 ifZero ifNonZero =>
    movePtr 1 3 ++
    ifZeroElse 3 13 14 15 16
      (movePtr 3 1 ++ setHere ifZero ++ movePtr 1 3)
      ([.dec_val] ++ movePtr 3 1 ++ setHere ifNonZero ++ movePtr 1 3) ++
    movePtr 3 1
  | .halt =>
    movePtr 1 0 ++ clearHere ++
    movePtr 0 1

/--
One dispatch window: skip entirely if another window already matched (the
`done` flag is set); otherwise test the `pc` cell — if it is `0`, mark `done`
and run `block` (which sets the new `pc`), and if it is not `0`, decrement
`pc`.
-/
def window (block : Program) : Program :=
  ifZeroElse 4 5 6 7 8
    (movePtr 4 1 ++
      ifZeroElse 1 9 10 11 12
        (movePtr 1 4 ++ [.inc_val] ++ movePtr 4 1 ++ block)
        [.dec_val] ++
      movePtr 1 4)
    []

/--
Compile a whole Minsky program. The result is a single loop over the
`running` cell: reset `done`, dispatch over the `pc` cell through one window
per instruction, and if no window matched (the `pc` fell off the program)
stop running. Initial `running`/`pc`/`c1`/`c2` are provided by the initial
state.
-/
def compileProgram (m : Minsky.Program) : Program :=
  [.loop (
    movePtr 0 4 ++ clearHere ++
    List.flatten (m.map (window ∘ compileInstr)) ++
    ifZeroElse 4 5 6 7 8
      (movePtr 4 0 ++ clearHere ++ movePtr 0 4) [] ++
    movePtr 4 0
  )]

end Compiler

end LeanBF
