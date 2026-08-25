/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Idioms

/-!
# Idiom Tests

Kernel re-assertions of the Brainfuck idiom theorems, plus concrete runs of
the move, duplicate, and scan loops on small tapes.

## Main definitions

* `moveStart`: A tape holding `3` at the pointer and `2` beside it.
* `dupStart`: A tape holding `3` at the pointer and `2`, `1` beside it.
* `scanStart`: A tape whose first zero to the right is three cells along.
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

example : parse "[->+>+<<]" = dupLoop := parse_dupLoop

example : LoopFree [Instruction.dec_val, .inc_ptr, .inc_val, .inc_ptr,
    .inc_val, .dec_ptr, .dec_ptr] :=
  loop_free_dupLoopBody

example (a b c : Nat) (s : State) (ha : s.tape s.ptr = a + 1)
    (hb : s.tape (s.ptr + 1) = b) (hc : s.tape (s.ptr + 2) = c) :
    runSeq [Instruction.dec_val, .inc_ptr, .inc_val, .inc_ptr, .inc_val,
      .dec_ptr, .dec_ptr] s = dupLoopStep a b c s :=
  runSeq_dupLoopBody a b c s ha hb hc

example (a b c : Nat) (s : State) (ha : s.tape s.ptr = a)
    (hb : s.tape (s.ptr + 1) = b) (hc : s.tape (s.ptr + 2) = c) :
    RunsTo (dupLoop, s)
      { s with tape := (fun i =>
          if i = s.ptr then 0
          else if i = s.ptr + 1 then b + a
          else if i = s.ptr + 2 then c + a
          else s.tape i) } :=
  runsTo_dupLoop a b c s ha hb hc

/-- A concrete tape: `3` at the pointer, with `2` and `1` to its right. -/
def dupStart : State where
  ptr := 0
  tape := fun i => if i = 0 then 3 else if i = 1 then 2 else if i = 2 then 1 else 0
  input := []
  output := []

/-- The duplicate loop drains `3` into both neighbours, ending `0`, `5`, `4`. -/
example : ((run 40 dupLoop dupStart).map fun s => (s.ptr, s.tape 0, s.tape 1, s.tape 2))
    = some (0, 0, 5, 4) := by
  decide

example : parse "[>]" = scanLoop := parse_scanLoop

example : parse "[<]" = scanLeftLoop := parse_scanLeftLoop

example (k : Nat) (s : State) (hk : s.tape (s.ptr + (k : Int)) = 0)
    (hlt : ∀ j : Nat, j < k → s.tape (s.ptr + (j : Int)) ≠ 0) :
    RunsTo (scanLoop, s) { s with ptr := s.ptr + (k : Int) } :=
  runsTo_scanLoop k s hk hlt

example (k : Nat) (s : State) (hk : s.tape (s.ptr - (k : Int)) = 0)
    (hlt : ∀ j : Nat, j < k → s.tape (s.ptr - (j : Int)) ≠ 0) :
    RunsTo (scanLeftLoop, s) { s with ptr := s.ptr - (k : Int) } :=
  runsTo_scanLeftLoop k s hk hlt

/-- A tape that is nonzero for three cells and zero at the fourth. -/
def scanStart : State where
  ptr := 0
  tape := fun i => if i = 0 then 7 else if i = 1 then 9 else if i = 2 then 4 else 0
  input := []
  output := []

/-- The scan loop walks right to the first zero, three cells along, in the
    `2 * 3 + 1` steps the semantics predict. -/
example : ((run 20 scanLoop scanStart).map fun s => s.ptr) = some 3 := by
  decide

/-- The scan stops at the *first* zero, not a later one: starting on the zero
    itself the pointer does not move. -/
example : ((run 20 scanLoop { scanStart with ptr := 3 }).map fun s => s.ptr)
    = some 3 := by
  decide

end LeanBF.Tests
