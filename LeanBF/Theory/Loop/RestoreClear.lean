/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Compiler
import LeanBF.Core.Semantics
import Mathlib.Tactic.Ring
import LeanBF.Theory.Loop.Basics

/-!
# Restore Loop and Clear

The restore loop `[s4 - test +]` moves `s4` back into `test`, and the clear
loop `[-]` zeroes the current cell.

## Main definitions

* `restoreLoopBody`: The body of the restore loop.
* `restoreLoop`: The restore loop itself.
* `restoreLoopStep`: The state after one restore-loop iteration.
* `restoreLoopPost`: The state after the restore loop has run to completion.

## Theorems

* `loop_free_restoreLoopBody`: The restore-loop body is loop-free.
* `runSeq_restoreLoopBody`: The restore-loop body moves one unit from `s4`
  back to `test`.
* `run_restoreLoop`: The restore loop moves `s4` back into `test`.
* `run_clearHere`: The clear loop `[-]` clears the current cell.
-/

namespace LeanBF

/-- The body of the restore loop: one iteration decrements `s4` and
    increments `test`. -/
def restoreLoopBody (test s4 : Int) : Program :=
  [.dec_val] ++ (Compiler.movePtr s4 test ++ ([.inc_val] ++ Compiler.movePtr test s4))

/-- The restore loop: `[s4 - test +]`, moving `s4` back into `test`. -/
def restoreLoop (test s4 : Int) : Program :=
  [.loop (restoreLoopBody test s4)]

/-- The state after one iteration of the restore loop. -/
def restoreLoopStep (test s4 : Int) (a v : Nat) (s : State) : State :=
  { s with tape := fun i => if i = s4 then v else if i = test then a + 1 else s.tape i }

/-- The state after the restore loop has run to completion: `s4` is moved
    back into `test`. -/
def restoreLoopPost (test s4 : Int) (a v : Nat) (s : State) : State :=
  { s with tape := fun i => if i = s4 then 0 else if i = test then a + v else s.tape i }

/-- The restore loop body is loop-free. -/
theorem loop_free_restoreLoopBody (test s4 : Int) : LoopFree (restoreLoopBody test s4) := by
  unfold restoreLoopBody
  apply loop_free_append
  · exact loop_free_single .dec_val (by intro body h'; cases h')
  · apply loop_free_append
    · exact loop_free_movePtr s4 test
    · apply loop_free_append
      · exact loop_free_single .inc_val (by intro body h'; cases h')
      · exact loop_free_movePtr test s4

/-- Running the restore loop body once moves one unit from `s4` to `test`. -/
theorem runSeq_restoreLoopBody (test s4 : Int) (a v : Nat) (s : State)
    (hptr : s.ptr = s4) (hv : s.tape s4 = v + 1) (ha : s.tape test = a)
    (hsep : test ≠ s4) :
    runSeq (restoreLoopBody test s4) s = restoreLoopStep test s4 a v s := by
  let u1 : State := { s with tape := fun i => if i = s4 then v else s.tape i }
  have hu1 : runSeq [.dec_val] s = u1 := by
    apply State.ext
    · simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell, hptr]
    · funext i
      simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell]
      by_cases hi : i = s4
      · simp only [hi, hptr, hv, Nat.add_sub_cancel]
      · simp only [hptr, if_neg hi]
    · rfl
    · rfl
  have hu1ptr : u1.ptr = s4 := by simp only [u1, hptr]
  let u2 : State := { u1 with ptr := test }
  have hu2 : runSeq (Compiler.movePtr s4 test) u1 = u2 := by
    apply State.ext
    · simp only [u2, runSeq_movePtr_ptr s4 test u1 hu1ptr]
    · simp only [u2, runSeq_movePtr_tape s4 test u1]
    · rw [(runSeq_movePtr_io s4 test u1).1]
    · rw [(runSeq_movePtr_io s4 test u1).2]
  have hu2ptr : u2.ptr = test := rfl
  let u3 : State := { u2 with tape := fun i => if i = test then a + 1 else u2.tape i }
  have hu2tape_test : u2.tape test = a := by
    simp only [u2, u1]
    rw [if_neg hsep]
    exact ha
  have hu3 : runSeq [.inc_val] u2 = u3 := by
    apply State.ext
    · simp only [runSeq, stepOne, u3, State.incVal, State.modifyCell, hu2ptr]
    · funext i
      simp only [runSeq, stepOne, u3, State.incVal, State.modifyCell]
      by_cases hi : i = test
      · simp only [hi, hu2ptr, hu2tape_test, if_true]
      · simp only [hu2ptr, if_neg hi]
    · rfl
    · rfl
  have hu3ptr : u3.ptr = test := rfl
  let u4 : State := { u3 with ptr := s4 }
  have hu4 : runSeq (Compiler.movePtr test s4) u3 = u4 := by
    apply State.ext
    · simp only [u4, runSeq_movePtr_ptr test s4 u3 hu3ptr]
    · simp only [u4, runSeq_movePtr_tape test s4 u3]
    · rw [(runSeq_movePtr_io test s4 u3).1]
    · rw [(runSeq_movePtr_io test s4 u3).2]
  change runSeq
    ([.dec_val] ++ (Compiler.movePtr s4 test ++ ([.inc_val] ++ Compiler.movePtr test s4))) s =
    restoreLoopStep test s4 a v s
  rw [runSeq_append]
  rw [hu1]
  rw [runSeq_append]
  rw [hu2]
  rw [runSeq_append]
  rw [hu3]
  rw [hu4]
  apply State.ext
  · simp only [u4, restoreLoopStep, hptr]
  · funext i
    simp only [u4, u3, u2, u1, restoreLoopStep]
    by_cases h1i : i = s4
    · simp only [h1i, if_neg (Ne.symm hsep), if_true]
    · by_cases h2i : i = test
      · simp only [h2i, if_neg hsep, if_true]
      · simp only [if_neg h1i, if_neg h2i]
  · rfl
  · rfl

/-- The restore loop moves `s4` back into `test`: from a state with `s4`
    holding `v` and `test` holding `a`, it reaches a state with `s4` holding
    `0` and `test` holding `a + v`. -/
theorem run_restoreLoop (v a : Nat) (test s4 : Int) (s : State)
    (hptr : s.ptr = s4) (hv : s.tape s4 = v) (ha : s.tape test = a)
    (hsep : test ≠ s4) :
    ∃ n : Nat, run n (restoreLoop test s4) s = some (restoreLoopPost test s4 a v s) := by
  induction v generalizing a s with
  | zero =>
      refine ⟨1, ?_⟩
      have hzero : s.currentVal = 0 := by simp only [State.currentVal, hptr, hv]
      have hstep : step (restoreLoop test s4) s = some ([], s) := by
        simp only [restoreLoop, step, if_pos hzero]
      simp only [run, hstep]
      congr 1
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
        simpa only [s'] using (runSeq_restoreLoopBody test s4 a v s hptr hv ha hsep)
      rcases ih (a + 1) s' hs'ptr hs's4 hs'test with ⟨n, hn⟩
      refine ⟨1 + (restoreLoopBody test s4).length + n, ?_⟩
      rw [show 1 + (restoreLoopBody test s4).length + n =
        Nat.succ ((restoreLoopBody test s4).length + n) by
        rw [Nat.succ_eq_add_one]
        ring]
      change run (Nat.succ ((restoreLoopBody test s4).length + n))
        [.loop (restoreLoopBody test s4)] s = some (restoreLoopPost test s4 a (v + 1) s)
      simp only [run, step, if_neg hne]
      rw [List.append_nil]
      rw [run_append]
      · rw [hrunSeq]
        change run n (restoreLoop test s4) s' = some (restoreLoopPost test s4 a (v + 1) s)
        rw [hn]
        congr 1
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
      · exact loop_free_restoreLoopBody test s4

/-- The clear loop `[-]` clears the current cell to `0`. -/
theorem run_clearHere (v : Nat) (s : State) (hv : s.tape s.ptr = v) :
    ∃ n : Nat, run n Compiler.clearHere s =
      some { s with tape := fun i => if i = s.ptr then 0 else s.tape i } := by
  induction v generalizing s with
  | zero =>
      refine ⟨1, ?_⟩
      have hzero : s.currentVal = 0 := by simp only [State.currentVal, hv]
      have hstep : step Compiler.clearHere s = some ([], s) := by
        simp only [Compiler.clearHere, step, if_pos hzero]
      simp only [run, hstep]
      congr 1
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = s.ptr
        · simp only [hi, hv, if_true]
        · simp only [if_neg hi]
      · rfl
      · rfl
  | succ v ih =>
      have hne : s.currentVal ≠ 0 := by
        simp only [State.currentVal, hv]
        exact Nat.succ_ne_zero v
      let s' : State := { s with tape := fun i => if i = s.ptr then v else s.tape i }
      have hs' : s'.tape s'.ptr = v := by
        simp only [s']
        rw [if_true]
      rcases ih s' hs' with ⟨n, hn⟩
      refine ⟨2 + n, ?_⟩
      rw [show 2 + n = Nat.succ (1 + n) by
        rw [Nat.succ_eq_add_one]
        ring]
      simp only [Compiler.clearHere, run, step, if_neg hne]
      rw [List.append_nil]
      change run ([Instruction.dec_val].length + n)
        ([Instruction.dec_val] ++ [Instruction.loop [Instruction.dec_val]]) s =
        some { s with tape := fun i => if i = s.ptr then 0 else s.tape i }
      rw [run_append]
      · have hbody : runSeq [.dec_val] s = s' := by
          apply State.ext
          · simp only [runSeq, stepOne, s', State.decVal, State.modifyCell]
          · funext i
            simp only [runSeq, stepOne, s', State.decVal, State.modifyCell]
            by_cases hi : i = s.ptr
            · simp only [hi, hv, if_true, Nat.add_sub_cancel]
            · simp only [if_neg hi]
          · rfl
          · rfl
        rw [hbody]
        change run n Compiler.clearHere s' =
          some { s with tape := fun i => if i = s.ptr then 0 else s.tape i }
        rw [hn]
        congr 1
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = s.ptr
          · simp only [hi, hv, s', if_true]
          · simp only [if_neg hi, s']
        · rfl
        · rfl
      · exact loop_free_single .dec_val (by intro body h'; cases h')

end LeanBF
