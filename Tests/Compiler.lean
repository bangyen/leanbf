/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Compiler
import LeanBF.Core.Semantics

/-!
# Compiler Tests

Kernel `decide` re-assertions that the compiled primitives and the full
dispatch-loop program evolve the simulated tape correctly.

## Main definitions

* `mkState`: A state with the pointer, `running`, `pc`, `c1`, and `c2` in
  their dispatch-loop cells.
-/

namespace LeanBF.Tests

open LeanBF

/-- A state with the pointer at `p`, the `running` flag in cell 0, `pc` in
    cell 1, `c1` in cell 2, and `c2` in cell 3. -/
def mkState (p pc c1 c2 : Nat) : State :=
  { ptr := p,
    tape := fun i =>
      if i = 0 then 1 else
      if i = 1 then pc else
      if i = 2 then c1 else
      if i = 3 then c2 else 0,
    input := [], output := [] }

example : Compiler.movePtr 1 1 = [] :=
  rfl

example : Compiler.movePtr 0 1 = [.inc_ptr] :=
  rfl

example : Compiler.movePtr 2 0 = [.dec_ptr, .dec_ptr] :=
  rfl

-- `ifZeroElse` runs the then-body exactly once when the tested cell is zero.
example : (run 1000 (Compiler.ifZeroElse 2 5 6 7 8 [.inc_val] [.dec_val])
      (mkState 2 0 0 0)).map (fun s => s.tape 2) = some 1 := by
  decide

-- `ifZeroElse` runs the else-body exactly once when the tested cell is not
-- zero, and preserves the cell beforehand.
example : (run 1000 (Compiler.ifZeroElse 2 5 6 7 8 [.inc_val] [.dec_val])
      (mkState 2 0 3 0)).map (fun s => s.tape 2) = some 2 := by
  decide

-- `inc1`: increment `c1` and set `pc`.
example : (run 1000 (Compiler.compileInstr (.inc1 1)) (mkState 1 0 5 0)).map
      (fun s => (s.ptr, s.tape 1, s.tape 2)) = some (1, 1, 6) := by
  decide

-- `jzdec1` on a zero counter jumps without decrementing.
example : (run 1000 (Compiler.compileInstr (.jzdec1 0 4)) (mkState 1 0 0 0)).map
      (fun s => (s.tape 1, s.tape 2)) = some (0, 0) := by
  decide

-- `jzdec1` on a non-zero counter decrements and jumps.
example : (run 1000 (Compiler.compileInstr (.jzdec1 0 4)) (mkState 1 0 2 0)).map
      (fun s => (s.tape 1, s.tape 2)) = some (4, 1) := by
  decide

-- `jzdec2` on a non-zero counter decrements and jumps.
example : (run 1000 (Compiler.compileInstr (.jzdec2 0 4)) (mkState 1 0 0 3)).map
      (fun s => (s.tape 1, s.tape 3)) = some (4, 2) := by
  decide

-- `halt` clears the `running` flag.
example : (run 1000 (Compiler.compileInstr .halt) (mkState 1 0 0 0)).map
      (fun s => s.tape 0) = some 0 := by
  decide

-- The empty program halts immediately.
example : (run 4000 (Compiler.compileProgram []) (mkState 0 0 0 0)).map
      (fun s => (s.tape 0, s.tape 1)) = some (0, 0) := by
  decide

-- `[inc1 1, halt]`: the counter is incremented, then the machine halts.
example : (run 4000 (Compiler.compileProgram [.inc1 1, .halt]) (mkState 0 0 0 0)).map
      (fun s => (s.tape 0, s.tape 1, s.tape 2)) = some (0, 0, 1) := by
  decide

-- `[inc1 1, inc2 2, halt]`: both counters are incremented, then halts.
example : (run 4000 (Compiler.compileProgram [.inc1 1, .inc2 2, .halt])
      (mkState 0 0 0 0)).map
      (fun s => (s.tape 0, s.tape 1, s.tape 2, s.tape 3)) = some (0, 0, 1, 1) := by
  decide

-- `[jzdec1 2 2, halt]` from a non-zero counter: decrement then halt.
example : (run 4000 (Compiler.compileProgram [.jzdec1 2 2, .halt]) (mkState 0 0 2 0)).map
      (fun s => (s.tape 0, s.tape 1, s.tape 2)) = some (0, 0, 1) := by
  decide

-- `[jzdec1 2 2, halt]` from a zero counter: jump to the halt and do not
-- decrement.
example : (run 4000 (Compiler.compileProgram [.jzdec1 2 2, .halt]) (mkState 0 0 0 0)).map
      (fun s => (s.tape 0, s.tape 1, s.tape 2)) = some (0, 0, 0) := by
  decide

-- A larger counter value exercises the multi-iteration copy/flag/restore
-- loops inside `jzdec1`.
example : (run 4000 (Compiler.compileProgram [.jzdec1 3 3, .halt]) (mkState 0 0 5 0)).map
      (fun s => (s.tape 0, s.tape 1, s.tape 2)) = some (0, 1, 4) := by
  decide

-- A larger counter that is zero jumps straight to the halt.
example : (run 4000 (Compiler.compileProgram [.jzdec1 3 3, .halt]) (mkState 0 0 0 0)).map
      (fun s => (s.tape 0, s.tape 1, s.tape 2)) = some (0, 1, 0) := by
  decide

end LeanBF.Tests
