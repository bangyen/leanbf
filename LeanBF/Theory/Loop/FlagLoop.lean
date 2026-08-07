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
# Flag Loop

The flag loop `[s1 - s3 +]` computes whether a tested cell was zero: `s3`
holds `1` exactly when the cell was zero.

## Main definitions

* `flagLoopBody`: The body of the flag loop.
* `flagLoop`: The flag loop itself.
* `flagLoopStep`: The state after one flag-loop iteration.
* `flagLoopPost`: The state after the flag loop has run to completion.

## Theorems

* `loop_free_flagLoopBody`: The flag-loop body is loop-free.
* `runSeq_flagLoopBody`: The flag-loop body moves one unit from `s1` to `s3`.
* `run_flagLoop`: The flag loop sets `s3` to `1` iff the tested cell was
  zero.
-/

namespace LeanBF

/-- The body of the flag loop: one iteration decrements `s1` and `s3`. -/
def flagLoopBody (s1 s3 : Int) : Program :=
  [.dec_val] ++ (Compiler.movePtr s1 s3 ++ ([.dec_val] ++ Compiler.movePtr s3 s1))

/-- The flag loop: `[s1 - s3 -]`, clearing `s3` once per unit of `s1`. -/
def flagLoop (s1 s3 : Int) : Program :=
  [.loop (flagLoopBody s1 s3)]

/-- The state after one iteration of the flag loop. -/
def flagLoopStep (s1 s3 : Int) (v w : Nat) (s : State) : State :=
  { s with tape := fun i => if i = s1 then v else if i = s3 then w - 1 else s.tape i }

/-- The state after the flag loop has run to completion: `s3` is cleared once
    per unit of `s1`. -/
def flagLoopPost (s1 s3 : Int) (w v : Nat) (s : State) : State :=
  { s with tape := fun i => if i = s1 then 0 else if i = s3 then w - v else s.tape i }

/-- The flag loop body is loop-free. -/
theorem loop_free_flagLoopBody (s1 s3 : Int) : LoopFree (flagLoopBody s1 s3) := by
  unfold flagLoopBody
  apply loop_free_append
  · exact loop_free_single .dec_val (by intro body h'; cases h')
  · apply loop_free_append
    · exact loop_free_movePtr s1 s3
    · apply loop_free_append
      · exact loop_free_single .dec_val (by intro body h'; cases h')
      · exact loop_free_movePtr s3 s1

/-- Running the flag loop body once produces `flagLoopStep`. -/
theorem runSeq_flagLoopBody (s1 s3 : Int) (v w : Nat) (s : State)
    (hptr : s.ptr = s1) (hv : s.tape s1 = v + 1) (hw : s.tape s3 = w)
    (hsep : s1 ≠ s3) :
    runSeq (flagLoopBody s1 s3) s = flagLoopStep s1 s3 v w s := by
  let u1 : State := { s with tape := fun i => if i = s1 then v else s.tape i }
  have hu1 : runSeq [.dec_val] s = u1 := by
    apply State.ext
    · simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell, hptr]
    · funext i
      simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell]
      by_cases hi : i = s1
      · simp only [hi, hptr, hv, Nat.add_sub_cancel]
      · simp only [hptr, if_neg hi]
    · rfl
    · rfl
  have hu1ptr : u1.ptr = s1 := by simp only [u1, hptr]
  let u2 : State := { u1 with ptr := s3 }
  have hu2 : runSeq (Compiler.movePtr s1 s3) u1 = u2 := by
    apply State.ext
    · simp only [u2, runSeq_movePtr_ptr s1 s3 u1 hu1ptr]
    · simp only [u2, runSeq_movePtr_tape s1 s3 u1]
    · rw [(runSeq_movePtr_io s1 s3 u1).1]
    · rw [(runSeq_movePtr_io s1 s3 u1).2]
  have hu2ptr : u2.ptr = s3 := rfl
  let u3 : State := { u2 with tape := fun i => if i = s3 then w - 1 else u2.tape i }
  have hu2tape_s3 : u2.tape s3 = w := by
    simp only [u2, u1]
    rw [if_neg (Ne.symm hsep)]
    exact hw
  have hu3 : runSeq [.dec_val] u2 = u3 := by
    apply State.ext
    · simp only [runSeq, stepOne, u3, State.decVal, State.modifyCell, hu2ptr]
    · funext i
      simp only [runSeq, stepOne, u3, State.decVal, State.modifyCell]
      by_cases hi : i = s3
      · simp only [hi, hu2ptr, hu2tape_s3, if_true]
      · simp only [hu2ptr, if_neg hi]
    · rfl
    · rfl
  have hu3ptr : u3.ptr = s3 := rfl
  let u4 : State := { u3 with ptr := s1 }
  have hu4 : runSeq (Compiler.movePtr s3 s1) u3 = u4 := by
    apply State.ext
    · simp only [u4, runSeq_movePtr_ptr s3 s1 u3 hu3ptr]
    · simp only [u4, runSeq_movePtr_tape s3 s1 u3]
    · rw [(runSeq_movePtr_io s3 s1 u3).1]
    · rw [(runSeq_movePtr_io s3 s1 u3).2]
  change runSeq
    ([.dec_val] ++ (Compiler.movePtr s1 s3 ++ ([.dec_val] ++ Compiler.movePtr s3 s1))) s =
    flagLoopStep s1 s3 v w s
  rw [runSeq_append]
  rw [hu1]
  rw [runSeq_append]
  rw [hu2]
  rw [runSeq_append]
  rw [hu3]
  rw [hu4]
  apply State.ext
  · simp only [u4, flagLoopStep, hptr]
  · funext i
    simp only [u4, u3, u2, u1, flagLoopStep]
    by_cases h1i : i = s1
    · simp only [h1i, if_neg hsep, if_true]
    · by_cases h2i : i = s3
      · simp only [h2i, if_neg (Ne.symm hsep), if_true]
      · simp only [if_neg h1i, if_neg h2i]
  · rfl
  · rfl

/-- The flag loop clears `s3` once per unit of `s1`: from a state with
    `s1` holding `v` and `s3` holding `w`, it reaches a state with `s1`
    holding `0` and `s3` holding `w - v`. -/
theorem run_flagLoop (v w : Nat) (s1 s3 : Int) (s : State)
    (hptr : s.ptr = s1) (hv : s.tape s1 = v) (hw : s.tape s3 = w)
    (hsep : s1 ≠ s3) :
    ∃ n : Nat, run n (flagLoop s1 s3) s = some (flagLoopPost s1 s3 w v s) := by
  induction v generalizing w s with
  | zero =>
      refine ⟨1, ?_⟩
      have hzero : s.currentVal = 0 := by simp only [State.currentVal, hptr, hv]
      have hstep : step (flagLoop s1 s3) s = some ([], s) := by
        simp only [flagLoop, step, if_pos hzero]
      simp only [run, hstep]
      congr 1
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
      rcases ih (w - 1) s' hs'ptr hs's1 hs's3 with ⟨n, hn⟩
      refine ⟨1 + (flagLoopBody s1 s3).length + n, ?_⟩
      rw [show 1 + (flagLoopBody s1 s3).length + n = Nat.succ ((flagLoopBody s1 s3).length + n) by
        rw [Nat.succ_eq_add_one]
        ring]
      change run (Nat.succ ((flagLoopBody s1 s3).length + n))
        [.loop (flagLoopBody s1 s3)] s = some (flagLoopPost s1 s3 w (v + 1) s)
      simp only [run, step, if_neg hne]
      rw [List.append_nil]
      rw [run_append]
      · rw [hrunSeq]
        change run n (flagLoop s1 s3) s' = some (flagLoopPost s1 s3 w (v + 1) s)
        rw [hn]
        congr 1
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
      · exact loop_free_flagLoopBody s1 s3

end LeanBF
