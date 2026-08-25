/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Idioms

/-!
# Idiom Tests

Kernel re-assertions of the Brainfuck idiom theorems, plus a concrete run of
the move loop on a small tape.

## Main definitions

* `moveStart`: A tape holding `3` at the pointer and `2` beside it.
-/

namespace LeanBF.Tests

open LeanBF

example : parse "[-]" = Compiler.clearHere := parse_clearHere

example : parse "[->+<]" = moveLoop := parse_moveLoop

example : LoopFree [Instruction.dec_val, .inc_ptr, .inc_val, .dec_ptr] :=
  loop_free_moveLoopBody

example (a b : Nat) (s : State) (ha : s.tape s.ptr = a + 1)
    (hb : s.tape (s.ptr + 1) = b) :
    runSeq [Instruction.dec_val, .inc_ptr, .inc_val, .dec_ptr] s
      = moveLoopStep a b s :=
  runSeq_moveLoopBody a b s ha hb

example (a b : Nat) (s : State) (ha : s.tape s.ptr = a)
    (hb : s.tape (s.ptr + 1) = b) :
    RunsTo (moveLoop, s)
      { s with tape := fun i =>
          if i = s.ptr then 0 else if i = s.ptr + 1 then b + a else s.tape i } :=
  runsTo_moveLoop a b s ha hb

/-- A concrete tape: `3` at the pointer and `2` beside it. -/
def moveStart : State where
  ptr := 0
  tape := fun i => if i = 0 then 3 else if i = 1 then 2 else 0
  input := []
  output := []

/-- The move loop drains `3` into the `2` next door, ending at `0` and `5`. -/
example : ((run 20 moveLoop moveStart).map fun s => (s.ptr, s.tape 0, s.tape 1))
    = some (0, 0, 5) := by
  decide

end LeanBF.Tests
