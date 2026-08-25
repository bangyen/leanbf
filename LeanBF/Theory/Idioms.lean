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
cells and the idiom is the same three characters. `moveLoop` and `dupLoop`
are the first idioms with no compiled counterpart.

Cells hold unbounded `Nat`, so these loops carry no overflow side condition:
the destinations end at `b + a` (and `c + a`) for any starting values. The
source cell is left at `0` and the pointer returns to it, which is what
lets the idioms compose with whatever follows.

Both proofs run by induction on the source cell's value. The bodies
`- > + <` and `- > + > + < <` are loop-free, so one iteration is a `runSeq`
computation, and `RunsTo_append` chains it onto the recursive call. The
duplicate loop differs only in carrying a second neighbour through the
induction; the shape is otherwise the same, which is what the move loop
predicted.

The scan loops are the exception the other three predicted. `[>]` walks right
until it finds a zero, so unlike the draining loops it does not terminate on
every tape: a tape that is nonzero everywhere to the right runs forever.
`runsTo_scanLoop` therefore takes the distance `k` to a zero as a parameter,
with the hypothesis that no earlier cell is zero — without that minimality the
statement would be false, since the loop stops at the *first* zero it meets,
not at the one chosen. The induction is on `k` rather than on a cell's value,
and the pointer arithmetic is over `Int`, so the casts need `push_cast` where
the earlier proofs needed nothing. Divergence in the absence of a zero is not
proven here; only the terminating case is.

## Main definitions

* `moveLoop`: The move loop `[->+<]`, draining a cell into its right
  neighbour.
* `moveLoopStep`: The state after one iteration of the move loop.
* `dupLoop`: The duplicate loop `[->+>+<<]`, draining a cell into its two
  right neighbours.
* `dupLoopStep`: The state after one iteration of the duplicate loop.
* `scanLoop`: The scan loop `[>]`, walking right to the next zero cell.
* `scanLeftLoop`: The scan loop `[<]`, walking left to the next zero cell.

## Theorems

* `parse_clearHere`: `Compiler.clearHere` is what `[-]` parses to.
* `parse_moveLoop`: `moveLoop` is what `[->+<]` parses to.
* `loop_free_moveLoopBody`: The move loop's body contains no loop.
* `runSeq_moveLoopBody`: One iteration moves a single unit right.
* `runsTo_moveLoop`: The move loop empties a cell into its right neighbour.
* `parse_dupLoop`: `dupLoop` is what `[->+>+<<]` parses to.
* `loop_free_dupLoopBody`: The duplicate loop's body contains no loop.
* `runSeq_dupLoopBody`: One iteration adds a unit to each neighbour.
* `runsTo_dupLoop`: The duplicate loop empties a cell into both neighbours.
* `parse_scanLoop`: `scanLoop` is what `[>]` parses to.
* `parse_scanLeftLoop`: `scanLeftLoop` is what `[<]` parses to.
* `loop_free_scanBody`: The scan loop's body contains no loop.
* `loop_free_scanLeftBody`: The left scan loop's body contains no loop.
* `runsTo_scanLoop`: The scan loop stops on the nearest zero to the right.
* `runsTo_scanLeftLoop`: The left scan stops on the nearest zero to the left.
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

/-- The duplicate loop `[->+>+<<]`: drain the current cell into both of its
    right neighbours, leaving each raised by the drained amount. -/
def dupLoop : Program :=
  [.loop [.dec_val, .inc_ptr, .inc_val, .inc_ptr, .inc_val, .dec_ptr, .dec_ptr]]

/-- The state after one iteration of the duplicate loop: the pointer is back
    where it started, its cell is one lower, and both cells to its right are
    one higher. -/
def dupLoopStep (a b c : Nat) (s : State) : State :=
  { s with tape := (fun i =>
      if i = s.ptr then a
      else if i = s.ptr + 1 then b + 1
      else if i = s.ptr + 2 then c + 1
      else s.tape i) }

/-- `dupLoop` is what the source `[->+>+<<]` parses to. -/
theorem parse_dupLoop : parse "[->+>+<<]" = dupLoop := by
  rfl

/-- The duplicate loop's body contains no loop. -/
theorem loop_free_dupLoopBody :
    LoopFree [Instruction.dec_val, .inc_ptr, .inc_val, .inc_ptr, .inc_val,
      .dec_ptr, .dec_ptr] := by
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  refine loop_free_cons _ _ (by intro body h; cases h) ?_
  exact loop_free_single _ (by intro body h; cases h)

/-- One iteration of the duplicate loop adds a unit to each of the two cells
    on the right, leaving the pointer where it started. -/
theorem runSeq_dupLoopBody (a b c : Nat) (s : State)
    (ha : s.tape s.ptr = a + 1) (hb : s.tape (s.ptr + 1) = b)
    (hc : s.tape (s.ptr + 2) = c) :
    runSeq [Instruction.dec_val, .inc_ptr, .inc_val, .inc_ptr, .inc_val,
      .dec_ptr, .dec_ptr] s = dupLoopStep a b c s := by
  have hnorm : s.ptr + 1 + 1 = s.ptr + 2 := by ring
  have h1 : s.ptr + 1 ≠ s.ptr := by omega
  have h2 : s.ptr + 2 ≠ s.ptr := by omega
  have h21 : s.ptr + 2 ≠ s.ptr + 1 := by omega
  apply State.ext
  · simp only [runSeq, stepOne, State.decVal, State.incVal, State.modifyCell,
      State.incPtr, State.decPtr, dupLoopStep]
    ring
  · funext i
    simp only [runSeq, stepOne, State.decVal, State.incVal, State.modifyCell,
      State.incPtr, State.decPtr, dupLoopStep, hnorm]
    by_cases hi : i = s.ptr
    · simp only [hi, if_true, if_neg h1.symm, if_neg h2.symm, ha,
        Nat.add_sub_cancel]
    · by_cases hi1 : i = s.ptr + 1
      · simp only [hi1, if_neg h1, if_true, if_neg h21.symm, hb]
      · by_cases hi2 : i = s.ptr + 2
        · simp only [hi2, if_neg h2, if_neg h21, if_true, hc]
        · simp only [if_neg hi, if_neg hi1, if_neg hi2]
  · rfl
  · rfl

/-- The duplicate loop `[->+>+<<]` empties the current cell into both of its
    right neighbours: from `a` at the pointer and `b`, `c` beside it, it ends
    with `0`, `b + a` and `c + a`, the pointer back on the drained cell. -/
theorem runsTo_dupLoop (a b c : Nat) (s : State)
    (ha : s.tape s.ptr = a) (hb : s.tape (s.ptr + 1) = b)
    (hc : s.tape (s.ptr + 2) = c) :
    RunsTo (dupLoop, s)
      { s with tape := (fun i =>
          if i = s.ptr then 0
          else if i = s.ptr + 1 then b + a
          else if i = s.ptr + 2 then c + a
          else s.tape i) } := by
  induction a generalizing s b c with
  | zero =>
      have h1 : s.ptr + 1 ≠ s.ptr := by omega
      have h2 : s.ptr + 2 ≠ s.ptr := by omega
      have hzero : s.currentVal = 0 := by simp only [State.currentVal, ha]
      have hstep : step dupLoop s = some ([], s) := by
        simp only [dupLoop, step, if_pos hzero]
      have heq : { s with tape := (fun i =>
          if i = s.ptr then 0
          else if i = s.ptr + 1 then b + 0
          else if i = s.ptr + 2 then c + 0
          else s.tape i) } = s := by
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = s.ptr
          · simp only [hi, if_true, ha]
          · by_cases hi1 : i = s.ptr + 1
            · simp only [hi1, if_neg h1, if_true, hb, Nat.add_zero]
            · by_cases hi2 : i = s.ptr + 2
              · simp only [hi2, if_neg h2, if_neg (show s.ptr + 2 ≠ s.ptr + 1 by omega),
                  if_true, hc, Nat.add_zero]
              · simp only [if_neg hi, if_neg hi1, if_neg hi2]
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step dupLoop s s [] s hstep (RunsTo.halt s)
  | succ a ih =>
      have h1 : s.ptr + 1 ≠ s.ptr := by omega
      have h2 : s.ptr + 2 ≠ s.ptr := by omega
      have hnz : s.currentVal ≠ 0 := by
        simp only [State.currentVal, ha]
        exact Nat.succ_ne_zero a
      have hstep : step dupLoop s
          = some ([.dec_val, .inc_ptr, .inc_val, .inc_ptr, .inc_val,
              .dec_ptr, .dec_ptr] ++ dupLoop, s) := by
        simp only [dupLoop, step, if_neg hnz, List.append_nil]
      -- One iteration lands on `dupLoopStep`, which the induction consumes.
      let s' : State := dupLoopStep a b c s
      have hbody : RunsTo ([Instruction.dec_val, .inc_ptr, .inc_val, .inc_ptr,
          .inc_val, .dec_ptr, .dec_ptr], s) s' := by
        have h := runsTo_of_loopFree [Instruction.dec_val, .inc_ptr, .inc_val,
          .inc_ptr, .inc_val, .dec_ptr, .dec_ptr] s loop_free_dupLoopBody
        rwa [runSeq_dupLoopBody a b c s ha hb hc] at h
      have hptr' : s'.ptr = s.ptr := rfl
      have ha' : s'.tape s'.ptr = a := by
        simp only [s', dupLoopStep, if_true]
      have hb' : s'.tape (s'.ptr + 1) = b + 1 := by
        simp only [s', dupLoopStep, if_neg h1, if_true]
      have hc' : s'.tape (s'.ptr + 2) = c + 1 := by
        simp only [s', dupLoopStep, if_neg h2,
          if_neg (show s.ptr + 2 ≠ s.ptr + 1 by omega), if_true]
      have hrest : RunsTo (dupLoop, s')
          { s' with tape := (fun i =>
              if i = s'.ptr then 0
              else if i = s'.ptr + 1 then b + 1 + a
              else if i = s'.ptr + 2 then c + 1 + a
              else s'.tape i) } :=
        ih (b + 1) (c + 1) s' ha' hb' hc'
      have hfinal : { s' with tape := (fun i =>
            if i = s'.ptr then 0
            else if i = s'.ptr + 1 then b + 1 + a
            else if i = s'.ptr + 2 then c + 1 + a
            else s'.tape i) }
          = { s with tape := (fun i =>
            if i = s.ptr then 0
            else if i = s.ptr + 1 then b + (a + 1)
            else if i = s.ptr + 2 then c + (a + 1)
            else s.tape i) } := by
        apply State.ext
        · rfl
        · funext i
          simp only [s', dupLoopStep]
          by_cases hi : i = s.ptr
          · simp only [hi, if_true]
          · by_cases hi1 : i = s.ptr + 1
            · simp only [hi1, if_neg h1, if_true]
              ring
            · by_cases hi2 : i = s.ptr + 2
              · simp only [hi2, if_neg h2,
                  if_neg (show s.ptr + 2 ≠ s.ptr + 1 by omega), if_true]
                ring
              · simp only [if_neg hi, if_neg hi1, if_neg hi2]
        · rfl
        · rfl
      rw [hfinal] at hrest
      exact RunsTo.step dupLoop s s ([.dec_val, .inc_ptr, .inc_val, .inc_ptr,
        .inc_val, .dec_ptr, .dec_ptr] ++ dupLoop)
        _ hstep (RunsTo_append dupLoop s' _ hbody hrest)

/-- The scan loop `[>]`: walk right until the pointer finds a zero cell. -/
def scanLoop : Program :=
  [.loop [.inc_ptr]]

/-- The scan loop `[<]`: walk left until the pointer finds a zero cell. -/
def scanLeftLoop : Program :=
  [.loop [.dec_ptr]]

/-- `scanLoop` is what the source `[>]` parses to. -/
theorem parse_scanLoop : parse "[>]" = scanLoop := by
  rfl

/-- `scanLeftLoop` is what the source `[<]` parses to. -/
theorem parse_scanLeftLoop : parse "[<]" = scanLeftLoop := by
  rfl

/-- The scan loop's body contains no loop. -/
theorem loop_free_scanBody : LoopFree [Instruction.inc_ptr] :=
  loop_free_single _ (by intro body h; cases h)

/-- The left scan loop's body contains no loop. -/
theorem loop_free_scanLeftBody : LoopFree [Instruction.dec_ptr] :=
  loop_free_single _ (by intro body h; cases h)

/-- The scan loop `[>]` stops on the nearest zero cell to the right: given a
    zero `k` cells along with no zero before it, the loop ends with the pointer
    exactly there, and the tape untouched.

    The minimality hypothesis is essential, not decoration: the loop halts at
    the first zero it meets, so without it the pointer need not reach `k`. -/
theorem runsTo_scanLoop (k : Nat) (s : State)
    (hk : s.tape (s.ptr + (k : Int)) = 0)
    (hlt : ∀ j : Nat, j < k → s.tape (s.ptr + (j : Int)) ≠ 0) :
    RunsTo (scanLoop, s) { s with ptr := s.ptr + (k : Int) } := by
  induction k generalizing s with
  | zero =>
      have hzero : s.currentVal = 0 := by
        simp only [State.currentVal]
        simpa only [Nat.cast_zero, Int.add_zero] using hk
      have hstep : step scanLoop s = some ([], s) := by
        simp only [scanLoop, step, if_pos hzero]
      have heq : { s with ptr := s.ptr + ((0 : Nat) : Int) } = s := by
        apply State.ext
        · simp only [Nat.cast_zero, Int.add_zero]
        · rfl
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step scanLoop s s [] s hstep (RunsTo.halt s)
  | succ k ih =>
      have hnz : s.currentVal ≠ 0 := by
        simp only [State.currentVal]
        simpa only [Nat.cast_zero, Int.add_zero] using hlt 0 (by omega)
      have hstep : step scanLoop s = some ([.inc_ptr] ++ scanLoop, s) := by
        simp only [scanLoop, step, if_neg hnz, List.append_nil]
      -- One iteration is a single `>`, which moves the pointer and nothing else.
      have hbody : RunsTo ([Instruction.inc_ptr], s) s.incPtr := by
        have h := runsTo_of_loopFree [Instruction.inc_ptr] s loop_free_scanBody
        simpa only [runSeq, stepOne] using h
      have hk' : (s.incPtr).tape ((s.incPtr).ptr + (k : Int)) = 0 := by
        simp only [State.incPtr]
        rw [show s.ptr + 1 + (k : Int) = s.ptr + ((k + 1 : Nat) : Int) by push_cast; ring]
        exact hk
      have hlt' : ∀ j : Nat, j < k → (s.incPtr).tape ((s.incPtr).ptr + (j : Int)) ≠ 0 := by
        intro j hj
        simp only [State.incPtr]
        rw [show s.ptr + 1 + (j : Int) = s.ptr + ((j + 1 : Nat) : Int) by push_cast; ring]
        exact hlt (j + 1) (by omega)
      have hrest : RunsTo (scanLoop, s.incPtr)
          { s.incPtr with ptr := (s.incPtr).ptr + (k : Int) } := ih (s.incPtr) hk' hlt'
      have hfinal : { s.incPtr with ptr := (s.incPtr).ptr + (k : Int) }
          = { s with ptr := s.ptr + ((k + 1 : Nat) : Int) } := by
        apply State.ext
        · simp only [State.incPtr]
          push_cast
          ring
        · rfl
        · rfl
        · rfl
      rw [hfinal] at hrest
      exact RunsTo.step scanLoop s s ([.inc_ptr] ++ scanLoop) _ hstep
        (RunsTo_append scanLoop s.incPtr _ hbody hrest)

/-- The left scan loop `[<]` stops on the nearest zero cell to the left, the
    mirror of `runsTo_scanLoop`. This is the one idiom here that the repository
    already writes: `Examples.helloWorld` uses `[<]` to return to the start of
    its working cells. -/
theorem runsTo_scanLeftLoop (k : Nat) (s : State)
    (hk : s.tape (s.ptr - (k : Int)) = 0)
    (hlt : ∀ j : Nat, j < k → s.tape (s.ptr - (j : Int)) ≠ 0) :
    RunsTo (scanLeftLoop, s) { s with ptr := s.ptr - (k : Int) } := by
  induction k generalizing s with
  | zero =>
      have hzero : s.currentVal = 0 := by
        simp only [State.currentVal]
        simpa only [Nat.cast_zero, Int.sub_zero] using hk
      have hstep : step scanLeftLoop s = some ([], s) := by
        simp only [scanLeftLoop, step, if_pos hzero]
      have heq : { s with ptr := s.ptr - ((0 : Nat) : Int) } = s := by
        apply State.ext
        · simp only [Nat.cast_zero, Int.sub_zero]
        · rfl
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step scanLeftLoop s s [] s hstep (RunsTo.halt s)
  | succ k ih =>
      have hnz : s.currentVal ≠ 0 := by
        simp only [State.currentVal]
        simpa only [Nat.cast_zero, Int.sub_zero] using hlt 0 (by omega)
      have hstep : step scanLeftLoop s = some ([.dec_ptr] ++ scanLeftLoop, s) := by
        simp only [scanLeftLoop, step, if_neg hnz, List.append_nil]
      have hbody : RunsTo ([Instruction.dec_ptr], s) s.decPtr := by
        have h := runsTo_of_loopFree [Instruction.dec_ptr] s loop_free_scanLeftBody
        simpa only [runSeq, stepOne] using h
      have hk' : (s.decPtr).tape ((s.decPtr).ptr - (k : Int)) = 0 := by
        simp only [State.decPtr]
        rw [show s.ptr - 1 - (k : Int) = s.ptr - ((k + 1 : Nat) : Int) by push_cast; ring]
        exact hk
      have hlt' : ∀ j : Nat, j < k → (s.decPtr).tape ((s.decPtr).ptr - (j : Int)) ≠ 0 := by
        intro j hj
        simp only [State.decPtr]
        rw [show s.ptr - 1 - (j : Int) = s.ptr - ((j + 1 : Nat) : Int) by push_cast; ring]
        exact hlt (j + 1) (by omega)
      have hrest : RunsTo (scanLeftLoop, s.decPtr)
          { s.decPtr with ptr := (s.decPtr).ptr - (k : Int) } := ih (s.decPtr) hk' hlt'
      have hfinal : { s.decPtr with ptr := (s.decPtr).ptr - (k : Int) }
          = { s with ptr := s.ptr - ((k + 1 : Nat) : Int) } := by
        apply State.ext
        · simp only [State.decPtr]
          push_cast
          ring
        · rfl
        · rfl
        · rfl
      rw [hfinal] at hrest
      exact RunsTo.step scanLeftLoop s s ([.dec_ptr] ++ scanLeftLoop) _ hstep
        (RunsTo_append scanLeftLoop s.decPtr _ hbody hrest)

end LeanBF
