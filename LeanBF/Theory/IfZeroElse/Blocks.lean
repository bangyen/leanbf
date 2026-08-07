/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Semantics
import LeanBF.Theory.BodyLoop
import LeanBF.Theory.IfZeroElse.LoopRuns

/-!
# ifZeroElse Blocks

The primitive blocks that assemble `Compiler.ifZeroElse`: pointer movement,
moving-and-clearing, setting `s3` to `1`, clearing the scratch cells, and the
shared setup prefix and its state constructors.

## Main definitions

* `moveClearState`: Move to `b` and clear it, ending with the pointer on `b`.
* `setOneState`: The state after setting `s3` to `1` and moving to `s1`.
* `clearScratchState`: The state after clearing the four scratch cells.
* `clearScratch`: Clear the four scratch cells and return to `test`.
* `ifZeroElseSetup`: The shared prefix of `ifZeroElse`.
* `thenBodyState`: The state from which `thenBody` runs (`test` is `0`).
* `elseBodyState`: The state from which `elseBody` runs (`test` is `v`).
* `ifZeroElsePost`: The `ifZeroElse` final state.

## Theorems

* `runsTo_movePtr`: Move the pointer from `a` to `b` without changing the
  tape or I/O.
* `runsTo_move_clear`: Moving to `b` and clearing it zeroes `b`.
* `runsTo_setOne`: Set the `s3` cell to `1` and move to `s1`.
* `runsTo_clearScratch`: The scratch-clearing block zeroes the four scratch
  cells.
* `ifZeroElsePost_tape`: `ifZeroElsePost` preserves every cell outside the
  four scratch cells.
* `thenBodyState_tape`: `thenBodyState` preserves every cell outside the
  block's footprint.
* `elseBodyState_tape`: `elseBodyState` preserves every cell outside the
  block's footprint.
* `thenPost_eq`: The then-branch post state equals `thenBodyState`.
* `elsePost_eq`: The else-branch post state equals `elseBodyState`.
* `RunsTo_eq_program`: A `RunsTo` to equal programs is extensional.
-/

namespace LeanBF

/-- Move the pointer from `a` to `b` without changing the tape or I/O. -/
theorem runsTo_movePtr (a b : Int) (s : State) (hptr : s.ptr = a) :
    RunsTo (Compiler.movePtr a b, s) { s with ptr := b } := by
  have h1 : RunsTo (Compiler.movePtr a b, s) (runSeq (Compiler.movePtr a b) s) :=
    runsTo_of_loopFree (Compiler.movePtr a b) s (loop_free_movePtr a b)
  have h1s : runSeq (Compiler.movePtr a b) s = { s with ptr := b } := by
    apply State.ext
    · rw [runSeq_movePtr_ptr a b s hptr]
    · rw [runSeq_movePtr_tape a b s]
    · rw [(runSeq_movePtr_io a b s).1]
    · rw [(runSeq_movePtr_io a b s).2]
  rw [h1s] at h1
  exact h1

/-- Move to `b` and clear it, ending with the pointer on `b`. -/
def moveClearState (b : Int) (s : State) : State :=
  { s with ptr := b, tape := fun i => if i = b then 0 else s.tape i }

/-- Moving to `b` and clearing it zeroes `b`. -/
theorem runsTo_move_clear (a b : Int) (s : State) (hptr : s.ptr = a) :
    RunsTo (Compiler.movePtr a b ++ Compiler.clearHere, s) (moveClearState b s) := by
  have h1 : RunsTo (Compiler.movePtr a b, s) { s with ptr := b } :=
    runsTo_movePtr a b s hptr
  have h2 : RunsTo (Compiler.clearHere, { s with ptr := b }) (moveClearState b s) := by
    have hc : RunsTo (Compiler.clearHere, { s with ptr := b })
        { { s with ptr := b } with tape := fun i => if i = b then 0 else s.tape i } :=
      runsTo_clearHere (({ s with ptr := b }).tape ({ s with ptr := b }).ptr)
        ({ s with ptr := b }) rfl
    simpa only [moveClearState] using hc
  exact RunsTo_append Compiler.clearHere { s with ptr := b } (moveClearState b s) h1 h2

/-- The state after setting `s3` to `1` and moving to `s1`. -/
def setOneState (s1 s3 : Int) (s : State) : State :=
  { s with ptr := s1, tape := fun i => if i = s3 then 1 else s.tape i }

/-- Set the `s3` cell to `1` and move to `s1`. -/
theorem runsTo_setOne (test s1 s3 : Int) (s : State) (hptr : s.ptr = test)
    (h3 : s.tape s3 = 0) :
    RunsTo (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1, s)
      (setOneState s1 s3 s) := by
  have hl : LoopFree (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1) := by
    apply loop_free_append
    · apply loop_free_append
      · exact loop_free_movePtr test s3
      · exact loop_free_single .inc_val (by intro body h'; cases h')
    · exact loop_free_movePtr s3 s1
  have hb : RunsTo (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1, s)
      (runSeq (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1) s) :=
    runsTo_of_loopFree (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1) s hl
  have hs : runSeq (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1) s =
      setOneState s1 s3 s := by
    rw [runSeq_append, runSeq_append]
    have hstep1 : runSeq (Compiler.movePtr test s3) s = { s with ptr := s3 } := by
      apply State.ext
      · rw [runSeq_movePtr_ptr test s3 s hptr]
      · rw [runSeq_movePtr_tape test s3 s]
      · rw [(runSeq_movePtr_io test s3 s).1]
      · rw [(runSeq_movePtr_io test s3 s).2]
    rw [hstep1]
    have hstep2 : runSeq [.inc_val] { s with ptr := s3 } =
        { { s with ptr := s3 } with tape := fun i => if i = s3 then 1 else s.tape i } := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = s3
        · simp only [hi, runSeq, stepOne, State.incVal, State.modifyCell, if_true, h3,
          Nat.zero_add]
        · simp only [hi, runSeq, stepOne, State.incVal, State.modifyCell, if_false]
      · rfl
      · rfl
    rw [hstep2]
    apply State.ext
    · rw [runSeq_movePtr_ptr s3 s1 _ (by rfl)]
      rfl
    · rw [runSeq_movePtr_tape s3 s1 _]
      rfl
    · rw [(runSeq_movePtr_io s3 s1 _).1]
      rfl
    · rw [(runSeq_movePtr_io s3 s1 _).2]
      rfl
  rw [hs] at hb
  exact hb

/-- The state after clearing the four scratch cells and returning to `test`. -/
def clearScratchState (test s1 s2 s3 s4 : Int) (s : State) : State :=
  { s with ptr := test, tape := fun i =>
      if i = s1 then 0 else
      if i = s2 then 0 else
      if i = s3 then 0 else
      if i = s4 then 0 else s.tape i }

/-- Clear the four scratch cells and return to `test`. -/
def clearScratch (test s1 s2 s3 s4 : Int) : Program :=
  Compiler.movePtr test s1 ++ Compiler.clearHere ++
  Compiler.movePtr s1 s2 ++ Compiler.clearHere ++
  Compiler.movePtr s2 s3 ++ Compiler.clearHere ++
  Compiler.movePtr s3 s4 ++ Compiler.clearHere ++
  Compiler.movePtr s4 test

/-- The scratch-clearing block zeroes the four scratch cells. -/
theorem runsTo_clearScratch (test s1 s2 s3 s4 : Int) (s : State) (hptr : s.ptr = test)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4) :
    RunsTo (clearScratch test s1 s2 s3 s4, s) (clearScratchState test s1 s2 s3 s4 s) := by
  rcases hsep with ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
  let a1 : State := moveClearState s1 s
  let a2 : State := moveClearState s2 a1
  let a3 : State := moveClearState s3 a2
  let a4 : State := moveClearState s4 a3
  have h1 : RunsTo (Compiler.movePtr test s1 ++ Compiler.clearHere, s) a1 := by
    simpa only [a1] using runsTo_move_clear test s1 s hptr
  have ha1 : a1.ptr = s1 := by simp only [a1, moveClearState]
  have h2 : RunsTo (Compiler.movePtr s1 s2 ++ Compiler.clearHere, a1) a2 := by
    simpa only [a2] using runsTo_move_clear s1 s2 a1 ha1
  have ha2 : a2.ptr = s2 := by simp only [a2, moveClearState]
  have h3 : RunsTo (Compiler.movePtr s2 s3 ++ Compiler.clearHere, a2) a3 := by
    simpa only [a3] using runsTo_move_clear s2 s3 a2 ha2
  have ha3 : a3.ptr = s3 := by simp only [a3, moveClearState]
  have h4 : RunsTo (Compiler.movePtr s3 s4 ++ Compiler.clearHere, a3) a4 := by
    simpa only [a4] using runsTo_move_clear s3 s4 a3 ha3
  have ha4 : a4.ptr = s4 := by simp only [a4, moveClearState]
  have h5 : RunsTo (Compiler.movePtr s4 test, a4) { a4 with ptr := test } :=
    runsTo_movePtr s4 test a4 ha4
  have hChain : RunsTo (clearScratch test s1 s2 s3 s4, s) { a4 with ptr := test } := by
    simpa only [clearScratch, List.append_assoc] using
      (RunsTo_append (Compiler.movePtr s4 test) a4 { a4 with ptr := test }
        (RunsTo_append (Compiler.movePtr s3 s4 ++ Compiler.clearHere) a3 a4
          (RunsTo_append (Compiler.movePtr s2 s3 ++ Compiler.clearHere) a2 a3
            (RunsTo_append (Compiler.movePtr s1 s2 ++ Compiler.clearHere) a1 a2 h1 h2)
            h3)
          h4)
        h5)
  have hFinal : { a4 with ptr := test } = clearScratchState test s1 s2 s3 s4 s := by
    apply State.ext
    · rfl
    · funext i
      simp only [a4, a3, a2, a1, moveClearState, clearScratchState]
      by_cases h1i : i = s1
      · simp only [h1i, h14, h13, h12, if_false, if_true]
      · by_cases h2i : i = s2
        · simp only [h2i, h24, h23, Ne.symm h12, if_false, if_true]
        · by_cases h3i : i = s3
          · simp only [h3i, h34, Ne.symm h13, Ne.symm h23, if_false, if_true]
          · by_cases h4i : i = s4
            · simp only [h4i, Ne.symm h14, Ne.symm h24, Ne.symm h34, if_false, if_true]
            · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
    · rfl
    · rfl
  rw [hFinal] at hChain
  exact hChain

/-- The shared prefix of `ifZeroElse`: clear the scratch cells, copy `test`
    into the scratch cells, set `s3 := 1`, clear `s3` once per unit of `s1`,
    and restore `test`. -/
def ifZeroElseSetup (test s1 s2 s3 s4 : Int) : Program :=
  clearScratch test s1 s2 s3 s4 ++
  copyLoop test s1 s2 s4 ++
  (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1) ++
  flagLoop s1 s3 ++
  Compiler.movePtr s1 test ++
  Compiler.movePtr test s4 ++
  restoreLoop test s4 ++
  Compiler.movePtr s4 test

/-- The state from which `thenBody` runs (`test` is `0`). -/
def thenBodyState (test s1 s2 s3 s4 : Int) (s : State) : State :=
  { s with ptr := test, tape := fun i =>
      if i = test then 0 else
      if i = s1 then 0 else
      if i = s2 then 0 else
      if i = s3 then 1 else
      if i = s4 then 0 else s.tape i }

/-- The state from which `elseBody` runs (`test` is `v`). -/
def elseBodyState (test s1 s2 s3 s4 : Int) (v : Nat) (s : State) : State :=
  { s with ptr := test, tape := fun i =>
      if i = test then v else
      if i = s1 then 0 else
      if i = s2 then v else
      if i = s3 then 0 else
      if i = s4 then 0 else s.tape i }

/-- The `ifZeroElse` final state: pointer on `test` and all scratch cells
    cleared. -/
def ifZeroElsePost (test s1 s2 s3 s4 : Int) (s : State) : State :=
  { s with ptr := test, tape := fun i =>
      if i = s1 then 0 else
      if i = s2 then 0 else
      if i = s3 then 0 else
      if i = s4 then 0 else s.tape i }

/-- `ifZeroElsePost` preserves every cell outside the four scratch cells. -/
theorem ifZeroElsePost_tape (test s1 s2 s3 s4 : Int) (s : State) {i : Int}
    (h1 : i ≠ s1) (h2 : i ≠ s2) (h3 : i ≠ s3) (h4 : i ≠ s4) :
    (ifZeroElsePost test s1 s2 s3 s4 s).tape i = s.tape i := by
  simp only [ifZeroElsePost, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- `thenBodyState` preserves every cell outside the block's footprint. -/
theorem thenBodyState_tape (test s1 s2 s3 s4 : Int) (s : State) {i : Int}
    (h1 : i ≠ test) (h2 : i ≠ s1) (h3 : i ≠ s2) (h4 : i ≠ s3) (h5 : i ≠ s4) :
    (thenBodyState test s1 s2 s3 s4 s).tape i = s.tape i := by
  simp only [thenBodyState, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- `elseBodyState` preserves every cell outside the block's footprint. -/
theorem elseBodyState_tape (test s1 s2 s3 s4 : Int) (v : Nat) (s : State) {i : Int}
    (h1 : i ≠ test) (h2 : i ≠ s1) (h3 : i ≠ s2) (h4 : i ≠ s3) (h5 : i ≠ s4) :
    (elseBodyState test s1 s2 s3 s4 v s).tape i = s.tape i := by
  simp only [elseBodyState, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

lemma thenPost_eq (test s1 s2 s3 s4 : ℕ) (s_then : State)
    (h2 : s_then.tape s1 = 0) (h3 : s_then.tape s2 = 0)
    (h4 : s_then.tape s4 = 0)
    (i12 : (s1 : Int) ≠ (s2 : Int)) (i13 : (s1 : Int) ≠ (s3 : Int))
    (i14 : (s1 : Int) ≠ (s4 : Int)) (i23 : (s2 : Int) ≠ (s3 : Int))
    (i24 : (s2 : Int) ≠ (s4 : Int)) (i34 : (s3 : Int) ≠ (s4 : Int)) :
    { s_then with
      ptr := (test : Int), tape := fun i => if i = (s3 : Int) then 0 else s_then.tape i } =
    ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then := by
  apply State.ext
  · rfl
  · funext i
    simp only [ifZeroElsePost]
    by_cases h1i : i = (s1 : Int)
    · simp only [h1i, i13, if_false, if_true, h2]
    · by_cases h2i : i = (s2 : Int)
      · simp only [h2i, i23, Ne.symm i12, if_false, if_true, h3]
      · by_cases h3i : i = (s3 : Int)
        · simp only [h3i, Ne.symm i13, Ne.symm i23, if_false, if_true]
        · by_cases h4i : i = (s4 : Int)
          · simp only [h4i, Ne.symm i34, Ne.symm i14, Ne.symm i24, if_false, if_true, h4]
          · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
  · rfl
  · rfl

lemma elsePost_eq (test s1 s2 s3 s4 : ℕ) (s_else : State)
    (h2 : s_else.tape s1 = 0) (h3 : s_else.tape s3 = 0)
    (h4 : s_else.tape s4 = 0)
    (i12 : (s1 : Int) ≠ (s2 : Int)) (i13 : (s1 : Int) ≠ (s3 : Int))
    (i14 : (s1 : Int) ≠ (s4 : Int)) (i23 : (s2 : Int) ≠ (s3 : Int))
    (i24 : (s2 : Int) ≠ (s4 : Int)) (i34 : (s3 : Int) ≠ (s4 : Int)) :
    { s_else with
      ptr := (test : Int), tape := fun i => if i = (s2 : Int) then 0 else s_else.tape i } =
    ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else := by
  apply State.ext
  · rfl
  · funext i
    simp only [ifZeroElsePost]
    by_cases h1i : i = (s1 : Int)
    · simp only [h1i, i12, if_false, if_true, h2]
    · by_cases h2i : i = (s2 : Int)
      · simp only [h2i, Ne.symm i12, if_false, if_true]
      · by_cases h3i : i = (s3 : Int)
        · simp only [h3i, Ne.symm i23, Ne.symm i13, if_false, if_true, h3]
        · by_cases h4i : i = (s4 : Int)
          · simp only [h4i, Ne.symm i24, Ne.symm i14, Ne.symm i34, if_false, if_true, h4]
          · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
  · rfl
  · rfl

lemma RunsTo_eq_program {A B : Program} {s s' : State} (h : RunsTo (A, s) s')
    (heq : A = B) : RunsTo (B, s) s' := by
  rw [← heq]
  exact h

end LeanBF
