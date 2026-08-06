/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.BodyLoop

/-!
# The `ifZeroElse` Conditional

This module proves the behavior of `Compiler.ifZeroElse`, the value-preserving
conditional used by the dispatch loop. From a state with the pointer on the
`test` cell holding `v`, the compiled conditional runs `thenBody` exactly once
when `v = 0` and `elseBody` exactly once when `v ≠ 0`, preserving `test`,
zeroing the tested cell, and restoring all scratch cells to `0`.

The proof chains the four loop effects (`copyLoop`, `flagLoop`, `restoreLoop`,
and the `bodyLoop`) together with the `RunsTo_append` composition. The module
also records the `RunsTo` forms of the three fixed loops.

## Main definitions

* `moveClearState`: The state after moving to and clearing a cell.
* `setOneState`: The state after setting `s3` to `1` and moving to `s1`.
* `clearScratchState`: The state after clearing the four scratch cells.
* `clearScratch`: Clear the four scratch cells and return to `test`.
* `ifZeroElseSetup`: The shared prefix of `ifZeroElse` through the restore
  loop.
* `thenBodyState`: The state from which `thenBody` runs (`test` is `0`).
* `elseBodyState`: The state from which `elseBody` runs (`test` is `v`).
* `ifZeroElsePost`: The final state: pointer on `test` and all scratch cells
  cleared.

## Theorems

* `runsTo_copyLoop`: The copy loop moves the tested value into three cells
  (RunsTo form).
* `runsTo_flagLoop`: The flag loop clears `s3` once per unit of `s1`
  (RunsTo form).
* `runsTo_restoreLoop`: The restore loop moves `s4` back into `test`
  (RunsTo form).
* `runsTo_movePtr`: A pointer move changes only the pointer.
* `runsTo_move_clear`: Moving to a cell and clearing it zeroes it.
* `runsTo_setOne`: Setting `s3` to `1` and moving to `s1`.
* `runsTo_clearScratch`: The scratch-clearing block zeroes the four scratch
  cells.
* `thenPost_eq`: The `thenBody` post-state equals `ifZeroElsePost`.
* `elsePost_eq`: The `elseBody` post-state equals `ifZeroElsePost`.
* `RunsTo_eq_program`: A run survives replacing the program by an equal one.
* `runsTo_setup_zero`: The setup reaches the `thenBodyState` when `test` is
  zero.
* `runsTo_setup_succ`: The setup reaches the `elseBodyState` when `test` is
  non-zero.
* `ifZeroElse_eq_chain`: `Compiler.ifZeroElse` equals the setup chained with
  the two body loops.
* `runsTo_ifZeroElse_zero`: A zero tested cell runs `thenBody` exactly once.
* `runsTo_ifZeroElse_succ`: A non-zero tested cell runs `elseBody` exactly
  once.
* `run_ifZeroElse_zero`: The zero case (run form).
* `run_ifZeroElse_succ`: The non-zero case (run form).
* `runToCompletion_ifZeroElse_zero`: The zero case (fuel-capped form).
* `runToCompletion_ifZeroElse_succ`: The non-zero case (fuel-capped form).
-/

namespace LeanBF

/-- The copy loop moves the tested value into three cells (RunsTo form). -/
theorem runsTo_copyLoop (v : Nat) (test s1 s2 s4 : Int) (a b c : Nat) (s : State)
    (hptr : s.ptr = test) (hv : s.tape test = v) (h1 : s.tape s1 = a)
    (h2 : s.tape s2 = b) (h4 : s.tape s4 = c)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s4 ∧ s1 ≠ s2 ∧ s1 ≠ s4 ∧ s2 ≠ s4) :
    RunsTo (copyLoop test s1 s2 s4, s) (copyLoopPost test s1 s2 s4 a b c v s) := by
  induction v generalizing a b c s with
  | zero =>
      have hzero : s.currentVal = 0 := by
        simp only [State.currentVal, hptr, hv]
      have hstep : step (copyLoop test s1 s2 s4) s = some ([], s) := by
        simp only [copyLoop, step, if_pos hzero]
      have heq : copyLoopPost test s1 s2 s4 a b c 0 s = s := by
        apply State.ext
        · rfl
        · funext i
          simp only [copyLoopPost]
          by_cases h1i : i = test
          · simp only [h1i, if_true, hv]
          · by_cases h2i : i = s1
            · simp only [h2i, if_neg (Ne.symm hsep.1), if_true, h1, Nat.add_zero]
            · by_cases h3i : i = s2
              · simp only [h3i, if_neg (Ne.symm hsep.2.1), if_neg (Ne.symm hsep.2.2.2.1),
                  if_true, h2, Nat.add_zero]
              · by_cases h4i : i = s4
                · simp only [h4i, if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
                    if_neg (Ne.symm hsep.2.2.2.2.2), if_true, h4, Nat.add_zero]
                · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step (copyLoop test s1 s2 s4) s s [] s hstep (RunsTo.halt s)
  | succ v ih =>
      let s' := copyLoopStep test s1 s2 s4 a b c v s
      have hs'ptr : s'.ptr = test := by simp only [s', copyLoopStep, hptr]
      have hs'test : s'.tape test = v := by
        simp only [s', copyLoopStep]
        rfl
      have hs's1 : s'.tape s1 = a + 1 := by
        simp only [s', copyLoopStep]
        rw [if_neg (Ne.symm hsep.1), if_true]
      have hs's2 : s'.tape s2 = b + 1 := by
        simp only [s', copyLoopStep]
        rw [if_neg (Ne.symm hsep.2.1), if_neg (Ne.symm hsep.2.2.2.1), if_true]
      have hs's4 : s'.tape s4 = c + 1 := by
        simp only [s', copyLoopStep]
        rw [if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
          if_neg (Ne.symm hsep.2.2.2.2.2), if_true]
      have hne : s.currentVal ≠ 0 := by
        simp only [State.currentVal, hptr, hv]
        exact Nat.succ_ne_zero v
      have hrunSeq : runSeq (copyLoopBody test s1 s2 s4) s = s' := by
        simpa only [s'] using
          (runSeq_copyLoopBody test s1 s2 s4 a b c v s hptr hv h1 h2 h4 hsep)
      have hbody : RunsTo (copyLoopBody test s1 s2 s4, s) s' := by
        have hb : RunsTo (copyLoopBody test s1 s2 s4, s) (runSeq (copyLoopBody test s1 s2 s4) s) :=
          runsTo_of_loopFree (copyLoopBody test s1 s2 s4) s (loop_free_copyLoopBody test s1 s2 s4)
        rw [hrunSeq] at hb
        exact hb
      have hstep : step (copyLoop test s1 s2 s4) s =
          some (copyLoopBody test s1 s2 s4 ++ [.loop (copyLoopBody test s1 s2 s4)], s) := by
        simp only [copyLoop, step, if_neg hne, List.append_nil]
      have ih' : RunsTo (copyLoop test s1 s2 s4, s')
          (copyLoopPost test s1 s2 s4 (a + 1) (b + 1) (c + 1) v s') :=
        ih (a + 1) (b + 1) (c + 1) s' hs'ptr hs'test hs's1 hs's2 hs's4
      have hchain : RunsTo (copyLoopBody test s1 s2 s4 ++ [.loop (copyLoopBody test s1 s2 s4)], s)
          (copyLoopPost test s1 s2 s4 (a + 1) (b + 1) (c + 1) v s') :=
        RunsTo_append [.loop (copyLoopBody test s1 s2 s4)] s'
          (copyLoopPost test s1 s2 s4 (a + 1) (b + 1) (c + 1) v s') hbody ih'
      have hpost : copyLoopPost test s1 s2 s4 (a + 1) (b + 1) (c + 1) v s' =
          copyLoopPost test s1 s2 s4 a b c (v + 1) s := by
        apply State.ext
        · rfl
        · funext i
          simp only [copyLoopPost, copyLoopStep, s']
          by_cases h1i : i = test
          · simp only [h1i, if_true]
          · by_cases h2i : i = s1
            · simp only [h2i, if_neg (Ne.symm hsep.1), if_true]
              ring
            · by_cases h3i : i = s2
              · simp only [h3i, if_neg (Ne.symm hsep.2.1), if_neg (Ne.symm hsep.2.2.2.1), if_true]
                ring
              · by_cases h4i : i = s4
                · simp only [h4i, if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
                    if_neg (Ne.symm hsep.2.2.2.2.2), if_true]
                  ring
                · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
        · rfl
        · rfl
      rw [hpost] at hchain
      exact RunsTo.step (copyLoop test s1 s2 s4) s s
        (copyLoopBody test s1 s2 s4 ++ [.loop (copyLoopBody test s1 s2 s4)])
        (copyLoopPost test s1 s2 s4 a b c (v + 1) s) hstep hchain

/-- The flag loop clears `s3` once per unit of `s1` (RunsTo form). -/
theorem runsTo_flagLoop (v w : Nat) (s1 s3 : Int) (s : State)
    (hptr : s.ptr = s1) (hv : s.tape s1 = v) (hw : s.tape s3 = w)
    (hsep : s1 ≠ s3) :
    RunsTo (flagLoop s1 s3, s) (flagLoopPost s1 s3 w v s) := by
  induction v generalizing w s with
  | zero =>
      have hzero : s.currentVal = 0 := by
        simp only [State.currentVal, hptr, hv]
      have hstep : step (flagLoop s1 s3) s = some ([], s) := by
        simp only [flagLoop, step, if_pos hzero]
      have heq : flagLoopPost s1 s3 w 0 s = s := by
        apply State.ext
        · rfl
        · funext i
          simp only [flagLoopPost]
          by_cases h1i : i = s1
          · simp only [h1i, if_true, hv]
          · by_cases h2i : i = s3
            · simp only [h2i, if_neg (Ne.symm hsep), if_true, hw, Nat.sub_zero]
            · simp only [if_neg h1i, if_neg h2i]
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step (flagLoop s1 s3) s s [] s hstep (RunsTo.halt s)
  | succ v ih =>
      let s' := flagLoopStep s1 s3 v w s
      have hs'ptr : s'.ptr = s1 := by simp only [s', flagLoopStep, hptr]
      have hs's1 : s'.tape s1 = v := by
        simp only [s', flagLoopStep]
        rw [if_true]
      have hs's3 : s'.tape s3 = w - 1 := by
        simp only [s', flagLoopStep]
        rw [if_neg (Ne.symm hsep), if_true]
      have hne : s.currentVal ≠ 0 := by
        simp only [State.currentVal, hptr, hv]
        exact Nat.succ_ne_zero v
      have hrunSeq : runSeq (flagLoopBody s1 s3) s = s' := by
        simpa only [s'] using (runSeq_flagLoopBody s1 s3 v w s hptr hv hw hsep)
      have hbody : RunsTo (flagLoopBody s1 s3, s) s' := by
        have hb : RunsTo (flagLoopBody s1 s3, s) (runSeq (flagLoopBody s1 s3) s) :=
          runsTo_of_loopFree (flagLoopBody s1 s3) s (loop_free_flagLoopBody s1 s3)
        rw [hrunSeq] at hb
        exact hb
      have hstep : step (flagLoop s1 s3) s =
          some (flagLoopBody s1 s3 ++ [.loop (flagLoopBody s1 s3)], s) := by
        simp only [flagLoop, step, if_neg hne, List.append_nil]
      have ih' : RunsTo (flagLoop s1 s3, s')
          (flagLoopPost s1 s3 (w - 1) v s') :=
        ih (w - 1) s' hs'ptr hs's1 hs's3
      have hchain : RunsTo (flagLoopBody s1 s3 ++ [.loop (flagLoopBody s1 s3)], s)
          (flagLoopPost s1 s3 (w - 1) v s') :=
        RunsTo_append [.loop (flagLoopBody s1 s3)] s'
          (flagLoopPost s1 s3 (w - 1) v s') hbody ih'
      have hpost : flagLoopPost s1 s3 (w - 1) v s' = flagLoopPost s1 s3 w (v + 1) s := by
        apply State.ext
        · rfl
        · funext i
          simp only [flagLoopPost, flagLoopStep, s']
          by_cases h1i : i = s1
          · simp only [h1i, if_true]
          · by_cases h2i : i = s3
            · simp only [h2i, if_neg (Ne.symm hsep), if_true]
              rw [Nat.sub_sub, Nat.add_comm 1 v]
            · simp only [if_neg h1i, if_neg h2i]
        · rfl
        · rfl
      rw [hpost] at hchain
      exact RunsTo.step (flagLoop s1 s3) s s
        (flagLoopBody s1 s3 ++ [.loop (flagLoopBody s1 s3)])
        (flagLoopPost s1 s3 w (v + 1) s) hstep hchain

/-- The restore loop moves `s4` back into `test` (RunsTo form). -/
theorem runsTo_restoreLoop (v a : Nat) (test s4 : Int) (s : State)
    (hptr : s.ptr = s4) (hv : s.tape s4 = v) (ha : s.tape test = a)
    (hsep : test ≠ s4) :
    RunsTo (restoreLoop test s4, s) (restoreLoopPost test s4 a v s) := by
  induction v generalizing a s with
  | zero =>
      have hzero : s.currentVal = 0 := by
        simp only [State.currentVal, hptr, hv]
      have hstep : step (restoreLoop test s4) s = some ([], s) := by
        simp only [restoreLoop, step, if_pos hzero]
      have heq : restoreLoopPost test s4 a 0 s = s := by
        apply State.ext
        · rfl
        · funext i
          simp only [restoreLoopPost]
          by_cases h1i : i = s4
          · simp only [h1i, if_true, hv]
          · by_cases h2i : i = test
            · simp only [h2i, if_neg hsep, if_true, ha, Nat.add_zero]
            · simp only [if_neg h1i, if_neg h2i]
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step (restoreLoop test s4) s s [] s hstep (RunsTo.halt s)
  | succ v ih =>
      let s' := restoreLoopStep test s4 a v s
      have hs'ptr : s'.ptr = s4 := by simp only [s', restoreLoopStep, hptr]
      have hs's4 : s'.tape s4 = v := by
        simp only [s', restoreLoopStep]
        rw [if_true]
      have hs'test : s'.tape test = a + 1 := by
        simp only [s', restoreLoopStep]
        rw [if_neg hsep, if_true]
      have hne : s.currentVal ≠ 0 := by
        simp only [State.currentVal, hptr, hv]
        exact Nat.succ_ne_zero v
      have hrunSeq : runSeq (restoreLoopBody test s4) s = s' := by
        simpa only [s'] using
          (runSeq_restoreLoopBody test s4 a v s hptr hv ha hsep)
      have hbody : RunsTo (restoreLoopBody test s4, s) s' := by
        have hb : RunsTo (restoreLoopBody test s4, s) (runSeq (restoreLoopBody test s4) s) :=
          runsTo_of_loopFree (restoreLoopBody test s4) s (loop_free_restoreLoopBody test s4)
        rw [hrunSeq] at hb
        exact hb
      have hstep : step (restoreLoop test s4) s =
          some (restoreLoopBody test s4 ++ [.loop (restoreLoopBody test s4)], s) := by
        simp only [restoreLoop, step, if_neg hne, List.append_nil]
      have ih' : RunsTo (restoreLoop test s4, s')
          (restoreLoopPost test s4 (a + 1) v s') :=
        ih (a + 1) s' hs'ptr hs's4 hs'test
      have hchain : RunsTo (restoreLoopBody test s4 ++ [.loop (restoreLoopBody test s4)], s)
          (restoreLoopPost test s4 (a + 1) v s') :=
        RunsTo_append [.loop (restoreLoopBody test s4)] s'
          (restoreLoopPost test s4 (a + 1) v s') hbody ih'
      have hpost : restoreLoopPost test s4 (a + 1) v s' = restoreLoopPost test s4 a (v + 1) s := by
        apply State.ext
        · rfl
        · funext i
          simp only [restoreLoopPost, restoreLoopStep, s']
          by_cases h1i : i = s4
          · simp only [h1i, if_true]
          · by_cases h2i : i = test
            · simp only [h2i, if_neg hsep, if_true]
              ring
            · simp only [if_neg h1i, if_neg h2i]
        · rfl
        · rfl
      rw [hpost] at hchain
      exact RunsTo.step (restoreLoop test s4) s s
        (restoreLoopBody test s4 ++ [.loop (restoreLoopBody test s4)])
        (restoreLoopPost test s4 a (v + 1) s) hstep hchain

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

/-- The setup reaches the `thenBodyState` when `test` is zero. -/
theorem runsTo_setup_zero (test s1 s2 s3 s4 : Int) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4) :
    RunsTo (ifZeroElseSetup test s1 s2 s3 s4, s0) (thenBodyState test s1 s2 s3 s4 s0) := by
  rcases hsep with ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
  let sC : State := clearScratchState test s1 s2 s3 s4 s0
  let sF : State := setOneState s1 s3 sC
  let sG : State := { sF with ptr := test }
  let sH : State := { sG with ptr := s4 }
  have hC : RunsTo (clearScratch test s1 s2 s3 s4, s0) sC := by
    have hc : RunsTo (clearScratch test s1 s2 s3 s4, s0)
        (clearScratchState test s1 s2 s3 s4 s0) :=
      runsTo_clearScratch test s1 s2 s3 s4 s0 hptr
          ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
    simpa only [sC] using hc
  have hsCptr : sC.ptr = test := by simp only [sC, clearScratchState]
  have hsCtest : sC.tape test = 0 := by
    simp only [sC, clearScratchState]
    rw [if_neg ht1, if_neg ht2, if_neg ht3, if_neg ht4]
    exact hv
  have hsCs1 : sC.tape s1 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_true]
  have hsCs2 : sC.tape s2 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_neg (Ne.symm h12), if_true]
  have hsCs3 : sC.tape s3 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_neg (Ne.symm h13), if_neg (Ne.symm h23), if_true]
  have hsCs4 : sC.tape s4 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_neg (Ne.symm h14), if_neg (Ne.symm h24), if_neg (Ne.symm h34), if_true]
  have hCopy : RunsTo (copyLoop test s1 s2 s4, sC) sC := by
    have hcp : RunsTo (copyLoop test s1 s2 s4, sC) (copyLoopPost test s1 s2 s4 0 0 0 0 sC) :=
      runsTo_copyLoop 0 test s1 s2 s4 0 0 0 sC hsCptr hsCtest hsCs1 hsCs2 hsCs4
        ⟨ht1, ht2, ht4, h12, h14, h24⟩
    have heq : copyLoopPost test s1 s2 s4 0 0 0 0 sC = sC := by
      apply State.ext
      · rfl
      · funext i
        simp only [copyLoopPost]
        by_cases h1i : i = test
        · simp only [h1i, if_true, hsCtest]
        · by_cases h2i : i = s1
          · simp only [h2i, if_neg (Ne.symm ht1), if_true, hsCs1, Nat.add_zero]
          · by_cases h3i : i = s2
            · simp only [h3i, if_neg (Ne.symm ht2), if_neg (Ne.symm h12), if_true,
                hsCs2, Nat.add_zero]
            · by_cases h4i : i = s4
              · simp only [h4i, if_neg (Ne.symm ht4), if_neg (Ne.symm h14),
                  if_neg (Ne.symm h24), if_true, hsCs4, Nat.add_zero]
              · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
      · rfl
      · rfl
    rw [heq] at hcp
    exact hcp
  have hSetOne : RunsTo
      (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1, sC) sF := by
    have hset : RunsTo (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1, sC)
        (setOneState s1 s3 sC) :=
      runsTo_setOne test s1 s3 sC hsCptr hsCs3
    simpa only [sF] using hset
  have hsFptr : sF.ptr = s1 := by simp only [sF, setOneState]
  have hsFs1 : sF.tape s1 = 0 := by simp only [sF, setOneState, hsCs1, h13, if_false]
  have hsFs3 : sF.tape s3 = 1 := by simp only [sF, setOneState, if_true]
  have hFlag : RunsTo (flagLoop s1 s3, sF) sF := by
    have hf : RunsTo (flagLoop s1 s3, sF) (flagLoopPost s1 s3 1 0 sF) :=
      runsTo_flagLoop 0 1 s1 s3 sF hsFptr hsFs1 hsFs3 h13
    have heq : flagLoopPost s1 s3 1 0 sF = sF := by
      apply State.ext
      · rfl
      · funext i
        simp only [flagLoopPost]
        by_cases h1i : i = s1
        · simp only [h1i, if_true, hsFs1]
        · by_cases h2i : i = s3
          · simp only [h2i, if_neg (Ne.symm h13), if_true, hsFs3, Nat.sub_zero]
          · simp only [if_neg h1i, if_neg h2i]
      · rfl
      · rfl
    rw [heq] at hf
    exact hf
  have hG : RunsTo (Compiler.movePtr s1 test, sF) sG := by
    simpa only [sG] using runsTo_movePtr s1 test sF hsFptr
  have hsGptr : sG.ptr = test := by simp only [sG]
  have hH : RunsTo (Compiler.movePtr test s4, sG) sH := by
    have hm : RunsTo (Compiler.movePtr test s4, sG) { sG with ptr := s4 } :=
      runsTo_movePtr test s4 sG hsGptr
    simpa only [sH] using hm
  have hsHptr : sH.ptr = s4 := by simp only [sH]
  have hsHtest : sH.tape test = 0 := by
    simp only [sH, sG, sF, sC, setOneState, clearScratchState]
    rw [if_neg ht3, if_neg ht1, if_neg ht2, if_neg ht3, if_neg ht4]
    exact hv
  have hsHs4 : sH.tape s4 = 0 := by
    simp only [sH, sG, sF, sC, setOneState, clearScratchState]
    rw [if_neg (Ne.symm h34), if_neg (Ne.symm h14), if_neg (Ne.symm h24),
      if_neg (Ne.symm h34), if_true]
  have hRestore : RunsTo (restoreLoop test s4, sH) sH := by
    have hr : RunsTo (restoreLoop test s4, sH) (restoreLoopPost test s4 0 0 sH) :=
      runsTo_restoreLoop 0 0 test s4 sH hsHptr hsHs4 hsHtest ht4
    have heq : restoreLoopPost test s4 0 0 sH = sH := by
      apply State.ext
      · rfl
      · funext i
        simp only [restoreLoopPost]
        by_cases h1i : i = s4
        · simp only [h1i, if_true, hsHs4]
        · by_cases h2i : i = test
          · simp only [h2i, if_neg ht4, if_true, hsHtest, Nat.add_zero]
          · simp only [if_neg h1i, if_neg h2i]
      · rfl
      · rfl
    rw [heq] at hr
    exact hr
  have hFinal : RunsTo (Compiler.movePtr s4 test, sH)
      (thenBodyState test s1 s2 s3 s4 s0) := by
    have hm : RunsTo (Compiler.movePtr s4 test, sH) { sH with ptr := test } :=
      runsTo_movePtr s4 test sH hsHptr
    have heq : { sH with ptr := test } = thenBodyState test s1 s2 s3 s4 s0 := by
      apply State.ext
      · rfl
      · funext i
        simp only [sH, sG, sF, sC, setOneState, clearScratchState, thenBodyState]
        by_cases h1i : i = test
        · simp only [h1i, ht3, ht1, ht2, ht4, hv, if_true, if_false]
        · by_cases h2i : i = s1
          · simp only [h2i, h13, Ne.symm ht1, if_true, if_false]
          · by_cases h3i : i = s2
            · simp only [h3i, h23, Ne.symm h12, Ne.symm ht2, if_true, if_false]
            · by_cases h4i : i = s3
              · simp only [h4i, Ne.symm ht3, Ne.symm h13, Ne.symm h23, if_true, if_false]
              · by_cases h5i : i = s4
                · simp only [h5i, Ne.symm h34, Ne.symm h14, Ne.symm h24, Ne.symm ht4,
                    if_true, if_false]
                · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i, if_neg h5i]
      · rfl
      · rfl
    rw [heq] at hm
    exact hm
  -- compose the setup segments
  have hprog : ifZeroElseSetup test s1 s2 s3 s4 =
      (((((((clearScratch test s1 s2 s3 s4 ++ copyLoop test s1 s2 s4)
        ++ (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1))
        ++ flagLoop s1 s3) ++ Compiler.movePtr s1 test)
        ++ Compiler.movePtr test s4) ++ restoreLoop test s4)
        ++ Compiler.movePtr s4 test) := by
    rfl
  have hchain :=
    (RunsTo_append (Compiler.movePtr s4 test) sH (thenBodyState test s1 s2 s3 s4 s0)
      (RunsTo_append (restoreLoop test s4) sH sH
        (RunsTo_append (Compiler.movePtr test s4) sG sH
          (RunsTo_append (Compiler.movePtr s1 test) sF sG
            (RunsTo_append (flagLoop s1 s3) sF sF
              (RunsTo_append
                (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1) sC sF
                (RunsTo_append (copyLoop test s1 s2 s4) sC sC hC hCopy) hSetOne)
              hFlag)
            hG)
          hH)
        hRestore)
      hFinal)
  exact RunsTo_eq_program hchain hprog.symm

/-- The setup reaches the `elseBodyState` when `test` is non-zero. -/
theorem runsTo_setup_succ (w : Nat) (test s1 s2 s3 s4 : Int) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape test = w + 1)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4) :
    RunsTo (ifZeroElseSetup test s1 s2 s3 s4, s0) (elseBodyState test s1 s2 s3 s4 (w + 1) s0) := by
  rcases hsep with ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
  let sC : State := clearScratchState test s1 s2 s3 s4 s0
  let sB : State := copyLoopPost test s1 s2 s4 0 0 0 (w + 1) sC
  let sF : State := setOneState s1 s3 sB
  let sK : State := flagLoopPost s1 s3 1 (w + 1) sF
  let sL : State := { sK with ptr := test }
  let sM : State := { sL with ptr := s4 }
  let sN : State := restoreLoopPost test s4 0 (w + 1) sM
  have hC : RunsTo (clearScratch test s1 s2 s3 s4, s0) sC := by
    have hc : RunsTo (clearScratch test s1 s2 s3 s4, s0)
        (clearScratchState test s1 s2 s3 s4 s0) :=
      runsTo_clearScratch test s1 s2 s3 s4 s0 hptr
          ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
    simpa only [sC] using hc
  have hsCptr : sC.ptr = test := by simp only [sC, clearScratchState]
  have hsCtest : sC.tape test = w + 1 := by
    simp only [sC, clearScratchState]
    rw [if_neg ht1, if_neg ht2, if_neg ht3, if_neg ht4]
    exact hv
  have hsCs1 : sC.tape s1 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_true]
  have hsCs2 : sC.tape s2 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_neg (Ne.symm h12), if_true]
  have hsCs3 : sC.tape s3 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_neg (Ne.symm h13), if_neg (Ne.symm h23), if_true]
  have hsCs4 : sC.tape s4 = 0 := by
    simp only [sC, clearScratchState]
    rw [if_neg (Ne.symm h14), if_neg (Ne.symm h24), if_neg (Ne.symm h34), if_true]
  have hCopy : RunsTo (copyLoop test s1 s2 s4, sC) sB := by
    have hcp : RunsTo (copyLoop test s1 s2 s4, sC) (copyLoopPost test s1 s2 s4 0 0 0 (w + 1) sC) :=
      runsTo_copyLoop (w + 1) test s1 s2 s4 0 0 0 sC hsCptr hsCtest hsCs1 hsCs2 hsCs4
        ⟨ht1, ht2, ht4, h12, h14, h24⟩
    simpa only [sB] using hcp
  have hsBptr : sB.ptr = test := by simp only [sB, copyLoopPost, hsCptr]
  have hsBtest : sB.tape test = 0 := by
    simp only [sB, copyLoopPost]
    rw [if_true]
  have hsBs1 : sB.tape s1 = w + 1 := by
    simp only [sB, copyLoopPost]
    rw [if_neg (Ne.symm ht1), if_true, Nat.zero_add]
  have hsBs2 : sB.tape s2 = w + 1 := by
    simp only [sB, copyLoopPost]
    rw [if_neg (Ne.symm ht2), if_neg (Ne.symm h12), if_true, Nat.zero_add]
  have hsBs3 : sB.tape s3 = 0 := by
    simp only [sB, copyLoopPost]
    rw [if_neg (Ne.symm ht3), if_neg (Ne.symm h13), if_neg (Ne.symm h23), if_neg h34, hsCs3]
  have hsBs4 : sB.tape s4 = w + 1 := by
    simp only [sB, copyLoopPost]
    rw [if_neg (Ne.symm ht4), if_neg (Ne.symm h14), if_neg (Ne.symm h24)]
    simp only [if_true, Nat.zero_add]
  have hSetOne : RunsTo
      (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1, sB) sF := by
    have hset : RunsTo (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1, sB)
        (setOneState s1 s3 sB) :=
      runsTo_setOne test s1 s3 sB hsBptr hsBs3
    simpa only [sF] using hset
  have hsFptr : sF.ptr = s1 := by simp only [sF, setOneState]
  have hsFs1 : sF.tape s1 = w + 1 := by simp only [sF, setOneState, hsBs1, h13, if_false]
  have hsFs3 : sF.tape s3 = 1 := by simp only [sF, setOneState, if_true]
  have hFlag : RunsTo (flagLoop s1 s3, sF) sK := by
    have hf : RunsTo (flagLoop s1 s3, sF) (flagLoopPost s1 s3 1 (w + 1) sF) :=
      runsTo_flagLoop (w + 1) 1 s1 s3 sF hsFptr hsFs1 hsFs3 h13
    simpa only [sK] using hf
  have hsKptr : sK.ptr = s1 := by simp only [sK, flagLoopPost, hsFptr]
  have hsKs1 : sK.tape s1 = 0 := by
    simp only [sK, flagLoopPost]
    rw [if_true]
  have hsKs3 : sK.tape s3 = 0 := by
    simp only [sK, flagLoopPost]
    rw [if_neg (Ne.symm h13), if_true, Nat.sub_eq_zero_of_le (Nat.succ_le_succ (Nat.zero_le w))]
  have hL : RunsTo (Compiler.movePtr s1 test, sK) sL := by
    have hm : RunsTo (Compiler.movePtr s1 test, sK) { sK with ptr := test } :=
      runsTo_movePtr s1 test sK hsKptr
    simpa only [sL] using hm
  have hsLptr : sL.ptr = test := by simp only [sL]
  have hM : RunsTo (Compiler.movePtr test s4, sL) sM := by
    have hm : RunsTo (Compiler.movePtr test s4, sL) { sL with ptr := s4 } :=
      runsTo_movePtr test s4 sL hsLptr
    simpa only [sM] using hm
  have hsMptr : sM.ptr = s4 := by simp only [sM]
  have hsMs4 : sM.tape s4 = w + 1 := by
    simp only [sM, sL, sK, sF, sB, sC, setOneState, clearScratchState, flagLoopPost, copyLoopPost]
    simp only [Ne.symm h34, Ne.symm ht4, Ne.symm h14, Ne.symm h24, if_true, if_false,
      Nat.zero_add]
  have hsMtest : sM.tape test = 0 := by
    simp only [sM, sL, sK, sF, sB, sC, setOneState, clearScratchState, flagLoopPost, copyLoopPost]
    simp only [ht1, ht2, ht3, ht4, if_true, if_false]
  have hRestore : RunsTo (restoreLoop test s4, sM) sN := by
    have hr : RunsTo (restoreLoop test s4, sM) (restoreLoopPost test s4 0 (w + 1) sM) :=
      runsTo_restoreLoop (w + 1) 0 test s4 sM hsMptr hsMs4 hsMtest ht4
    simpa only [sN] using hr
  have hsNptr : sN.ptr = s4 := by simp only [sN, restoreLoopPost, hsMptr]
  have hFinal : RunsTo (Compiler.movePtr s4 test, sN)
      (elseBodyState test s1 s2 s3 s4 (w + 1) s0) := by
    have hm : RunsTo (Compiler.movePtr s4 test, sN) { sN with ptr := test } :=
      runsTo_movePtr s4 test sN hsNptr
    have heq : { sN with ptr := test } = elseBodyState test s1 s2 s3 s4 (w + 1) s0 := by
      apply State.ext
      · rfl
      · funext i
        simp only [sN, sM, sL, sK, sF, sB, sC, setOneState, clearScratchState,
          flagLoopPost, copyLoopPost, restoreLoopPost, elseBodyState]
        by_cases h1i : i = test
        · simp only [h1i, ht4, if_false, if_true, Nat.zero_add]
        · by_cases h2i : i = s1
          · simp only [h2i, Ne.symm ht1, h14, if_true, if_false]
          · by_cases h3i : i = s2
            · simp only [h3i, Ne.symm ht2, Ne.symm h12, h24, h23, if_true, if_false,
                Nat.zero_add]
            · by_cases h4i : i = s3
              · simp only [h4i, h34, Ne.symm h13, Ne.symm h23, Ne.symm ht3, if_true, if_false,
                  Nat.sub_eq_zero_of_le (Nat.succ_le_succ (Nat.zero_le w))]
              · by_cases h5i : i = s4
                · simp only [h5i, Ne.symm ht4, Ne.symm h14, Ne.symm h24, Ne.symm h34,
                    if_false, if_true]
                · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i, if_neg h5i]
      · rfl
      · rfl
    rw [heq] at hm
    exact hm
  have hprog : ifZeroElseSetup test s1 s2 s3 s4 =
      (((((((clearScratch test s1 s2 s3 s4 ++ copyLoop test s1 s2 s4)
        ++ (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1))
        ++ flagLoop s1 s3) ++ Compiler.movePtr s1 test)
        ++ Compiler.movePtr test s4) ++ restoreLoop test s4)
        ++ Compiler.movePtr s4 test) := by
    rfl
  have hchain :=
    (RunsTo_append (Compiler.movePtr s4 test) sN (elseBodyState test s1 s2 s3 s4 (w + 1) s0)
      (RunsTo_append (restoreLoop test s4) sM sN
        (RunsTo_append (Compiler.movePtr test s4) sL sM
          (RunsTo_append (Compiler.movePtr s1 test) sK sL
            (RunsTo_append (flagLoop s1 s3) sF sK
              (RunsTo_append
                (Compiler.movePtr test s3 ++ [.inc_val] ++ Compiler.movePtr s3 s1) sB sF
                (RunsTo_append (copyLoop test s1 s2 s4) sC sB hC hCopy) hSetOne)
              hFlag)
            hL)
          hM)
        hRestore)
      hFinal)
  exact RunsTo_eq_program hchain hprog.symm

lemma ifZeroElse_eq_chain (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program) :
    Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody =
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) ++
        bodyLoop (test : Int) (s2 : Int) elseBody ++
        bodyLoop (test : Int) (s3 : Int) thenBody) := by
  simp only [Compiler.ifZeroElse, ifZeroElseSetup, clearScratch, copyLoop, copyLoopBody,
    flagLoop, flagLoopBody, restoreLoop, restoreLoopBody, bodyLoop, List.append_assoc]

/-- A zero tested cell runs `thenBody` exactly once, and the scratch cells are
    restored to `0`. -/
theorem runsTo_ifZeroElse_zero (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_then : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    RunsTo (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
  rcases hsep with ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
  have it1 : (test : Int) ≠ (s1 : Int) := fun h => ht1 (Int.ofNat.inj h)
  have it2 : (test : Int) ≠ (s2 : Int) := fun h => ht2 (Int.ofNat.inj h)
  have it3 : (test : Int) ≠ (s3 : Int) := fun h => ht3 (Int.ofNat.inj h)
  have it4 : (test : Int) ≠ (s4 : Int) := fun h => ht4 (Int.ofNat.inj h)
  have i12 : (s1 : Int) ≠ (s2 : Int) := fun h => h12 (Int.ofNat.inj h)
  have i13 : (s1 : Int) ≠ (s3 : Int) := fun h => h13 (Int.ofNat.inj h)
  have i14 : (s1 : Int) ≠ (s4 : Int) := fun h => h14 (Int.ofNat.inj h)
  have i23 : (s2 : Int) ≠ (s3 : Int) := fun h => h23 (Int.ofNat.inj h)
  have i24 : (s2 : Int) ≠ (s4 : Int) := fun h => h24 (Int.ofNat.inj h)
  have i34 : (s3 : Int) ≠ (s4 : Int) := fun h => h34 (Int.ofNat.inj h)
  let sT : State := thenBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0
  have hSetup : RunsTo
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0) sT := by
    have hs : RunsTo (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0)
        (thenBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0) :=
      runsTo_setup_zero (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0 hptr hv
        ⟨it1, it2, it3, it4, i12, i13, i14, i23, i24, i34⟩
    simpa only [sT] using hs
  have hsTptr : sT.ptr = (test : Int) := by simp only [sT, thenBodyState]
  have hsTzero : sT.tape (s2 : Int) = 0 := by
    simp only [sT, thenBodyState]
    rw [if_neg (Ne.symm it2), if_neg (Ne.symm i12), if_true]
  have hsTone : sT.tape (s3 : Int) = 0 + 1 := by
    simp only [sT, thenBodyState]
    rw [if_neg (Ne.symm it3), if_neg (Ne.symm i13), if_neg (Ne.symm i23), if_true]
  have hSkip : RunsTo (bodyLoop (test : Int) (s2 : Int) elseBody, sT) sT :=
    runsTo_bodyLoop_zero (test : Int) (s2 : Int) elseBody sT hsTptr hsTzero
  have hThen : RunsTo (bodyLoop (test : Int) (s3 : Int) thenBody, sT)
      { s_then with
        ptr := (test : Int), tape := fun i => if i = (s3 : Int) then 0 else s_then.tape i } :=
    runsTo_bodyLoop_succ 0 (test : Int) (s3 : Int) thenBody sT s_then hsTptr hsTone hthen h1
  have hprog : Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody =
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) ++
        bodyLoop (test : Int) (s2 : Int) elseBody ++ bodyLoop (test : Int) (s3 : Int) thenBody) :=
    ifZeroElse_eq_chain test s1 s2 s3 s4 thenBody elseBody
  have hThen' : RunsTo (bodyLoop (test : Int) (s3 : Int) thenBody, sT)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
    rw [thenPost_eq test s1 s2 s3 s4 s_then h2 h3 h4 i12 i13 i14 i23 i24 i34] at hThen
    exact hThen
  have hchain :=
    (RunsTo_append (bodyLoop (test : Int) (s3 : Int) thenBody) sT
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then)
      (RunsTo_append (bodyLoop (test : Int) (s2 : Int) elseBody) sT sT hSetup hSkip)
      hThen')
  exact RunsTo_eq_program hchain hprog.symm

/-- A non-zero tested cell runs `elseBody` exactly once, and the scratch cells
    are restored to `0`. -/
theorem runsTo_ifZeroElse_succ (w : Nat) (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_else : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = w + 1)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (helse : RunsTo (elseBody, elseBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) (w + 1) s0) s_else)
    (h1 : s_else.ptr = (test : Int)) (h2 : s_else.tape s1 = 0)
    (h3 : s_else.tape s3 = 0) (h4 : s_else.tape s4 = 0) :
    RunsTo (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
  rcases hsep with ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
  have it1 : (test : Int) ≠ (s1 : Int) := fun h => ht1 (Int.ofNat.inj h)
  have it2 : (test : Int) ≠ (s2 : Int) := fun h => ht2 (Int.ofNat.inj h)
  have it3 : (test : Int) ≠ (s3 : Int) := fun h => ht3 (Int.ofNat.inj h)
  have it4 : (test : Int) ≠ (s4 : Int) := fun h => ht4 (Int.ofNat.inj h)
  have i12 : (s1 : Int) ≠ (s2 : Int) := fun h => h12 (Int.ofNat.inj h)
  have i13 : (s1 : Int) ≠ (s3 : Int) := fun h => h13 (Int.ofNat.inj h)
  have i14 : (s1 : Int) ≠ (s4 : Int) := fun h => h14 (Int.ofNat.inj h)
  have i23 : (s2 : Int) ≠ (s3 : Int) := fun h => h23 (Int.ofNat.inj h)
  have i24 : (s2 : Int) ≠ (s4 : Int) := fun h => h24 (Int.ofNat.inj h)
  have i34 : (s3 : Int) ≠ (s4 : Int) := fun h => h34 (Int.ofNat.inj h)
  let sE : State := elseBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int)
      (w + 1) s0
  have hSetup : RunsTo
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0) sE := by
    have hs : RunsTo (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0)
        (elseBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) (w + 1) s0) :=
      runsTo_setup_succ w (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0 hptr hv
        ⟨it1, it2, it3, it4, i12, i13, i14, i23, i24, i34⟩
    simpa only [sE] using hs
  have hsEptr : sE.ptr = (test : Int) := by simp only [sE, elseBodyState]
  have hsEzero : sE.tape (s3 : Int) = 0 := by
    simp only [sE, elseBodyState]
    rw [if_neg (Ne.symm it3), if_neg (Ne.symm i13), if_neg (Ne.symm i23), if_true]
  have hsEone : sE.tape (s2 : Int) = w + 1 := by
    simp only [sE, elseBodyState]
    rw [if_neg (Ne.symm it2), if_neg (Ne.symm i12), if_true]
  have hElse : RunsTo (bodyLoop (test : Int) (s2 : Int) elseBody, sE)
      { s_else with
        ptr := (test : Int), tape := fun i => if i = (s2 : Int) then 0 else s_else.tape i } :=
    runsTo_bodyLoop_succ w (test : Int) (s2 : Int) elseBody sE s_else hsEptr hsEone helse h1
  have hprog : Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody =
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) ++
        bodyLoop (test : Int) (s2 : Int) elseBody ++ bodyLoop (test : Int) (s3 : Int) thenBody) :=
    ifZeroElse_eq_chain test s1 s2 s3 s4 thenBody elseBody
  have hElse' : RunsTo (bodyLoop (test : Int) (s2 : Int) elseBody, sE)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
    rw [elsePost_eq test s1 s2 s3 s4 s_else h2 h3 h4 i12 i13 i14 i23 i24 i34] at hElse
    exact hElse
  have hsPostptr :
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else).ptr
      = (test : Int) := by
    simp only [ifZeroElsePost]
  have hsPostzero :
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int)
        s_else).tape (s3 : Int)
      = 0 := by
    simp only [ifZeroElsePost]
    rw [if_neg (Ne.symm i13), if_neg (Ne.symm i23), if_true]
  have hSkip' : RunsTo (bodyLoop (test : Int) (s3 : Int) thenBody,
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else))
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) :=
    runsTo_bodyLoop_zero (test : Int) (s3 : Int) thenBody
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
      hsPostptr hsPostzero
  have hchain :=
    (RunsTo_append (bodyLoop (test : Int) (s3 : Int) thenBody)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
      (RunsTo_append (bodyLoop (test : Int) (s2 : Int) elseBody) sE
        (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
        hSetup hElse')
      hSkip')
  exact RunsTo_eq_program hchain hprog.symm

/-- A zero tested cell runs `thenBody` exactly once (run form). -/
theorem run_ifZeroElse_zero (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_then : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    ∃ fuel, RunsExactly fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
  exact run_of_RunsTo
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then)
    (runsTo_ifZeroElse_zero test s1 s2 s3 s4 thenBody elseBody s0 s_then hptr hv hsep hthen
      h1 h2 h3 h4)

/-- A non-zero tested cell runs `elseBody` exactly once (run form). -/
theorem run_ifZeroElse_succ (w : Nat) (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_else : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = w + 1)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (helse : RunsTo (elseBody, elseBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) (w + 1) s0) s_else)
    (h1 : s_else.ptr = (test : Int)) (h2 : s_else.tape s1 = 0)
    (h3 : s_else.tape s3 = 0) (h4 : s_else.tape s4 = 0) :
    ∃ fuel, RunsExactly fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
  exact run_of_RunsTo
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
    (runsTo_ifZeroElse_succ w test s1 s2 s3 s4 thenBody elseBody s0 s_else hptr hv hsep helse
      h1 h2 h3 h4)

/-- A zero tested cell runs `thenBody` exactly once (fuel-capped form). -/
theorem runToCompletion_ifZeroElse_zero (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_then : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    ∃ fuel, runToCompletion fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0 =
      some (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
  rcases run_ifZeroElse_zero test s1 s2 s3 s4 thenBody elseBody s0 s_then hptr hv hsep hthen
      h1 h2 h3 h4 with
    ⟨fuel, hrun, hfull⟩
  exact ⟨fuel + 1, runToCompletion_of_RunsExactly
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) fuel s0
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then)
    ⟨hrun, hfull⟩⟩

/-- A non-zero tested cell runs `elseBody` exactly once (fuel-capped form). -/
theorem runToCompletion_ifZeroElse_succ (w : Nat) (test s1 s2 s3 s4 : ℕ)
    (thenBody elseBody : Program)
    (s0 s_else : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = w + 1)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (helse : RunsTo (elseBody, elseBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) (w + 1) s0) s_else)
    (h1 : s_else.ptr = (test : Int)) (h2 : s_else.tape s1 = 0)
    (h3 : s_else.tape s3 = 0) (h4 : s_else.tape s4 = 0) :
    ∃ fuel, runToCompletion fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0 =
      some (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
  rcases run_ifZeroElse_succ w test s1 s2 s3 s4 thenBody elseBody s0 s_else hptr hv hsep helse
      h1 h2 h3 h4 with
    ⟨fuel, hrun, hfull⟩
  exact ⟨fuel + 1, runToCompletion_of_RunsExactly
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) fuel s0
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
    ⟨hrun, hfull⟩⟩

end LeanBF
