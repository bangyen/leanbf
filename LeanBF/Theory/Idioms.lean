/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Parser
import LeanBF.Theory.BodyLoop

/-!
# Brainfuck Idioms

Theorems about the loops a Brainfuck programmer actually writes, stated on
the literal instruction lists rather than on compiler output.

The rest of the development proves things about *compiled* programs: every
loop it reasons about is one `Core.Compiler` emitted, laid out over scratch
cells the compiler chose. Brainfuck source has its own small vocabulary —
`[-]` clears a cell, `[->+<]` moves one into its right neighbour — and this
module states those shapes directly, with the pointer's two cells as the
only parameters.

`[-]` is already covered: `runsTo_clearHere` (`Theory.BodyLoop.Basics`)
proves it, since the compiler emits `Compiler.clearHere` for its scratch
cells and the idiom is the same three characters. `moveLoop` is the first
idiom with no compiled counterpart.

Cells hold unbounded `Nat`, so the move loop carries no overflow side
condition: the destination ends at `b + a` for any starting values. The
source cell is left at `0` and the pointer returns to it, which is what
lets the idiom compose with whatever follows.

The proof runs by induction on the source cell's value. The body
`- > + <` is loop-free, so one iteration is a `runSeq` computation, and
`RunsTo_append` chains it onto the recursive call.

## Main definitions

* `moveLoop`: The move loop `[->+<]`, draining a cell into its right
  neighbour.
* `moveLoopStep`: The state after one iteration of the move loop.

## Theorems

* `parse_clearHere`: `Compiler.clearHere` is what `[-]` parses to.
* `parse_moveLoop`: `moveLoop` is what `[->+<]` parses to.
* `loop_free_moveLoopBody`: The move loop's body contains no loop.
* `runSeq_moveLoopBody`: One iteration moves a single unit right.
* `runsTo_moveLoop`: The move loop empties a cell into its right neighbour.
-/

namespace LeanBF

/-- The move loop `[->+<]`: drain the current cell into its right neighbour. -/
def moveLoop : Program :=
  [.loop [.dec_val, .inc_ptr, .inc_val, .dec_ptr]]

/-- The state after one iteration of the move loop: the pointer is back where
    it started, its cell is one lower, and the cell to its right is one
    higher. -/
def moveLoopStep (a b : Nat) (s : State) : State :=
  { s with tape := fun i =>
      if i = s.ptr then a else if i = s.ptr + 1 then b + 1 else s.tape i }

/-- `Compiler.clearHere` is what the source `[-]` parses to. The clear loop's
    semantics are already proven by `runsTo_clearHere`; this ties that theorem
    to the two characters a programmer would actually type. -/
theorem parse_clearHere : parse "[-]" = Compiler.clearHere := by
  rfl

/-- `moveLoop` is what the source `[->+<]` parses to. -/
theorem parse_moveLoop : parse "[->+<]" = moveLoop := by
  rfl

/-- The move loop's body contains no loop. -/
theorem loop_free_moveLoopBody :
    LoopFree [Instruction.dec_val, .inc_ptr, .inc_val, .dec_ptr] := by
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  exact loop_free_single _ (by intro body h; cases h)

/-- One iteration of the move loop moves a single unit into the cell on the
    right, leaving the pointer where it started. -/
theorem runSeq_moveLoopBody (a b : Nat) (s : State)
    (ha : s.tape s.ptr = a + 1) (hb : s.tape (s.ptr + 1) = b) :
    runSeq [Instruction.dec_val, .inc_ptr, .inc_val, .dec_ptr] s
      = moveLoopStep a b s := by
  have hne : s.ptr + 1 ≠ s.ptr := by omega
  apply State.ext
  · simp only [runSeq, stepOne, State.decVal, State.incVal, State.modifyCell,
      State.incPtr, State.decPtr, moveLoopStep]
    ring
  · funext i
    simp only [runSeq, stepOne, State.decVal, State.incVal, State.modifyCell,
      State.incPtr, State.decPtr, moveLoopStep]
    by_cases hi : i = s.ptr
    · simp only [hi, if_true, if_neg hne.symm, ha, Nat.add_sub_cancel]
    · by_cases hi1 : i = s.ptr + 1
      · simp only [hi1, if_neg hne, if_true, hb]
      · simp only [if_neg hi, if_neg hi1]
  · rfl
  · rfl

/-- The move loop `[->+<]` empties the current cell into its right neighbour:
    from `a` at the pointer and `b` beside it, it ends with `0` and `b + a`,
    with the pointer back on the drained cell. -/
theorem runsTo_moveLoop (a b : Nat) (s : State)
    (ha : s.tape s.ptr = a) (hb : s.tape (s.ptr + 1) = b) :
    RunsTo (moveLoop, s)
      { s with tape := fun i =>
          if i = s.ptr then 0 else if i = s.ptr + 1 then b + a else s.tape i } := by
  induction a generalizing s b with
  | zero =>
      have hne : s.ptr + 1 ≠ s.ptr := by omega
      have hzero : s.currentVal = 0 := by simp only [State.currentVal, ha]
      have hstep : step moveLoop s = some ([], s) := by
        simp only [moveLoop, step, if_pos hzero]
      have heq : { s with tape := fun i =>
          if i = s.ptr then 0 else if i = s.ptr + 1 then b + 0 else s.tape i } = s := by
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = s.ptr
          · simp only [hi, if_true, ha]
          · by_cases hi1 : i = s.ptr + 1
            · simp only [hi1, if_neg hne, if_true, hb, Nat.add_zero]
            · simp only [if_neg hi, if_neg hi1]
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step moveLoop s s [] s hstep (RunsTo.halt s)
  | succ a ih =>
      have hne : s.ptr + 1 ≠ s.ptr := by omega
      have hnz : s.currentVal ≠ 0 := by
        simp only [State.currentVal, ha]
        exact Nat.succ_ne_zero a
      have hstep : step moveLoop s
          = some ([.dec_val, .inc_ptr, .inc_val, .dec_ptr] ++ moveLoop, s) := by
        simp only [moveLoop, step, if_neg hnz, List.append_nil]
      -- One iteration lands on `moveLoopStep`, which the induction consumes.
      let s' : State := moveLoopStep a b s
      have hbody : RunsTo ([Instruction.dec_val, .inc_ptr, .inc_val, .dec_ptr], s) s' := by
        have h := runsTo_of_loopFree [Instruction.dec_val, .inc_ptr, .inc_val, .dec_ptr] s
          loop_free_moveLoopBody
        rwa [runSeq_moveLoopBody a b s ha hb] at h
      have hptr' : s'.ptr = s.ptr := rfl
      have ha' : s'.tape s'.ptr = a := by
        simp only [s', moveLoopStep, if_true]
      have hb' : s'.tape (s'.ptr + 1) = b + 1 := by
        simp only [s', moveLoopStep, if_neg hne, if_true]
      have hrest : RunsTo (moveLoop, s')
          { s' with tape := fun i =>
              if i = s'.ptr then 0 else if i = s'.ptr + 1 then b + 1 + a else s'.tape i } :=
        ih (b + 1) s' ha' hb'
      have hfinal : { s' with tape := fun i =>
            if i = s'.ptr then 0 else if i = s'.ptr + 1 then b + 1 + a else s'.tape i }
          = { s with tape := fun i =>
            if i = s.ptr then 0 else if i = s.ptr + 1 then b + (a + 1) else s.tape i } := by
        apply State.ext
        · rfl
        · funext i
          simp only [s', moveLoopStep]
          by_cases hi : i = s.ptr
          · simp only [hi, if_true]
          · by_cases hi1 : i = s.ptr + 1
            · simp only [hi1, if_neg hne, if_true]
              ring
            · simp only [if_neg hi, if_neg hi1]
        · rfl
        · rfl
      rw [hfinal] at hrest
      exact RunsTo.step moveLoop s s ([.dec_val, .inc_ptr, .inc_val, .dec_ptr] ++ moveLoop)
        _ hstep (RunsTo_append moveLoop s' _ hbody hrest)

end LeanBF
