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
# Copy Loop

The copy loop `[test - s1 + s2 + s4 +]`: one iteration decrements `test`
and increments `s1`, `s2`, and `s4`, and the whole loop copies `test` into
those cells.

## Main definitions

* `copyLoopBody`: The body of the copy loop.
* `copyLoop`: The copy loop itself.
* `copyLoopStep`: The state after one copy-loop iteration.
* `copyLoopPost`: The state after the copy loop has run to completion.
* `copyLoopBodyDec`: The tape after one copy-loop body iteration.

## Theorems

* `loop_free_copyLoopBody`: The copy-loop body is loop-free.
* `runSeq_copyLoopBody`: The copy-loop body moves one unit from `test` to the
  three target cells.
* `run_copyLoop`: The copy loop moves the tested cell into the target cells.
-/

namespace LeanBF

/-- The body of the copy loop: one iteration decrements `test` and
    increments `s1`, `s2`, and `s4`. -/
def copyLoopBody (test s1 s2 s4 : Int) : Program :=
  [.dec_val] ++
    (Compiler.movePtr test s1 ++
      ([.inc_val] ++
        (Compiler.movePtr s1 s2 ++
          ([.inc_val] ++
            (Compiler.movePtr s2 s4 ++
              ([.inc_val] ++ Compiler.movePtr s4 test))))))

/-- The copy loop: `[test - s1 + s2 + s4 +]`, moving the tested value into
    three cells. -/
def copyLoop (test s1 s2 s4 : Int) : Program :=
  [.loop (copyLoopBody test s1 s2 s4)]

/-- The state after one iteration of the copy loop. -/
def copyLoopStep (test s1 s2 s4 : Int) (a b c v : Nat) (s : State) : State :=
  { s with
    tape := fun i =>
      if i = test then v else
      if i = s1 then a + 1 else
      if i = s2 then b + 1 else
      if i = s4 then c + 1 else
      s.tape i }

/-- The state after the copy loop has run to completion. -/
def copyLoopPost (test s1 s2 s4 : Int) (a b c v : Nat) (s : State) : State :=
  { s with
    tape := fun i =>
      if i = test then 0 else
      if i = s1 then a + v else
      if i = s2 then b + v else
      if i = s4 then c + v else
      s.tape i }

/-- The copy loop body is loop-free. -/
theorem loop_free_copyLoopBody (test s1 s2 s4 : Int) :
    LoopFree (copyLoopBody test s1 s2 s4) := by
  unfold copyLoopBody
  apply loop_free_append
  · exact loop_free_single .dec_val (by intro body h'; cases h')
  · apply loop_free_append
    · exact loop_free_movePtr test s1
    · apply loop_free_append
      · exact loop_free_single .inc_val (by intro body h'; cases h')
      · apply loop_free_append
        · exact loop_free_movePtr s1 s2
        · apply loop_free_append
          · exact loop_free_single .inc_val (by intro body h'; cases h')
          · apply loop_free_append
            · exact loop_free_movePtr s2 s4
            · apply loop_free_append
              · exact loop_free_single .inc_val (by intro body h'; cases h')
              · exact loop_free_movePtr s4 test

/-- The state reached after the first cell write of the copy loop body: the
    tested cell is decremented. -/
def copyLoopBodyDec (test : Int) (v : Nat) (s : State) : State :=
  { s with tape := fun i => if i = test then v else s.tape i }

/-- Running the copy loop body once produces `copyLoopStep`. -/
theorem runSeq_copyLoopBody (test s1 s2 s4 : Int) (a b c v : Nat) (s : State)
    (hptr : s.ptr = test) (hv : s.tape test = v + 1)
    (h1 : s.tape s1 = a) (h2 : s.tape s2 = b) (h4 : s.tape s4 = c)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s4 ∧ s1 ≠ s2 ∧ s1 ≠ s4 ∧ s2 ≠ s4) :
    runSeq (copyLoopBody test s1 s2 s4) s = copyLoopStep test s1 s2 s4 a b c v s := by
  let u1 : State := { s with tape := fun i => if i = test then v else s.tape i }
  have hu1 : runSeq [.dec_val] s = u1 := by
    apply State.ext
    · simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell, hptr]
    · funext i
      simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell]
      by_cases hi : i = test
      · simp only [hi, hptr, hv, Nat.add_sub_cancel]
      · simp only [hptr, if_neg hi]
    · rfl
    · rfl
  have hu1ptr : u1.ptr = test := by simp only [u1, hptr]
  let u2 : State := { u1 with ptr := s1 }
  have hu2 : runSeq (Compiler.movePtr test s1) u1 = u2 := by
    apply State.ext
    · simp only [u2, runSeq_movePtr_ptr test s1 u1 hu1ptr]
    · simp only [u2, runSeq_movePtr_tape test s1 u1]
    · rw [(runSeq_movePtr_io test s1 u1).1]
    · rw [(runSeq_movePtr_io test s1 u1).2]
  have hu2ptr : u2.ptr = s1 := rfl
  have hu2tape_s1 : u2.tape s1 = a := by
    simp only [u2, u1]
    rw [if_neg (Ne.symm hsep.1)]
    exact h1
  let u3 : State := { u2 with tape := fun i => if i = s1 then a + 1 else u2.tape i }
  have hu3 : runSeq [.inc_val] u2 = u3 := by
    apply State.ext
    · simp only [runSeq, stepOne, u3, State.incVal, State.modifyCell, hu2ptr]
    · funext i
      simp only [runSeq, stepOne, u3, State.incVal, State.modifyCell]
      by_cases hi : i = s1
      · simp only [hi, hu2ptr, hu2tape_s1]
      · simp only [hu2ptr, if_neg hi]
    · rfl
    · rfl
  have hu3ptr : u3.ptr = s1 := rfl
  let u4 : State := { u3 with ptr := s2 }
  have hu4 : runSeq (Compiler.movePtr s1 s2) u3 = u4 := by
    apply State.ext
    · simp only [u4, runSeq_movePtr_ptr s1 s2 u3 hu3ptr]
    · simp only [u4, runSeq_movePtr_tape s1 s2 u3]
    · rw [(runSeq_movePtr_io s1 s2 u3).1]
    · rw [(runSeq_movePtr_io s1 s2 u3).2]
  have hu4ptr : u4.ptr = s2 := rfl
  have hu4tape_s2 : u4.tape s2 = b := by
    simp only [u4, u3, u2, u1]
    rw [if_neg (Ne.symm hsep.2.2.2.1), if_neg (Ne.symm hsep.2.1)]
    exact h2
  let u5 : State := { u4 with tape := fun i => if i = s2 then b + 1 else u4.tape i }
  have hu5 : runSeq [.inc_val] u4 = u5 := by
    apply State.ext
    · simp only [runSeq, stepOne, u5, State.incVal, State.modifyCell, hu4ptr]
    · funext i
      simp only [runSeq, stepOne, u5, State.incVal, State.modifyCell]
      by_cases hi : i = s2
      · simp only [hi, hu4ptr, hu4tape_s2]
      · simp only [hu4ptr, if_neg hi]
    · rfl
    · rfl
  have hu5ptr : u5.ptr = s2 := rfl
  let u6 : State := { u5 with ptr := s4 }
  have hu6 : runSeq (Compiler.movePtr s2 s4) u5 = u6 := by
    apply State.ext
    · simp only [u6, runSeq_movePtr_ptr s2 s4 u5 hu5ptr]
    · simp only [u6, runSeq_movePtr_tape s2 s4 u5]
    · rw [(runSeq_movePtr_io s2 s4 u5).1]
    · rw [(runSeq_movePtr_io s2 s4 u5).2]
  have hu6ptr : u6.ptr = s4 := rfl
  have hu6tape_s4 : u6.tape s4 = c := by
    simp only [u6, u5, u4, u3, u2, u1]
    rw [if_neg (Ne.symm hsep.2.2.2.2.2), if_neg (Ne.symm hsep.2.2.2.2.1),
      if_neg (Ne.symm hsep.2.2.1)]
    exact h4
  let u7 : State := { u6 with tape := fun i => if i = s4 then c + 1 else u6.tape i }
  have hu7 : runSeq [.inc_val] u6 = u7 := by
    apply State.ext
    · simp only [runSeq, stepOne, u7, State.incVal, State.modifyCell, hu6ptr]
    · funext i
      simp only [runSeq, stepOne, u7, State.incVal, State.modifyCell]
      by_cases hi : i = s4
      · simp only [hi, hu6ptr, hu6tape_s4]
      · simp only [hu6ptr, if_neg hi]
    · rfl
    · rfl
  have hu7ptr : u7.ptr = s4 := rfl
  let u8 : State := { u7 with ptr := test }
  have hu8 : runSeq (Compiler.movePtr s4 test) u7 = u8 := by
    apply State.ext
    · simp only [u8, runSeq_movePtr_ptr s4 test u7 hu7ptr]
    · simp only [u8, runSeq_movePtr_tape s4 test u7]
    · rw [(runSeq_movePtr_io s4 test u7).1]
    · rw [(runSeq_movePtr_io s4 test u7).2]
  -- peel the body and rewrite each segment
  change runSeq
    ([.dec_val] ++ (Compiler.movePtr test s1 ++
      ([.inc_val] ++ (Compiler.movePtr s1 s2 ++
        ([.inc_val] ++ (Compiler.movePtr s2 s4 ++
          ([.inc_val] ++ Compiler.movePtr s4 test))))))) s = copyLoopStep test s1 s2 s4 a b c v s
  rw [runSeq_append]
  rw [hu1]
  rw [runSeq_append]
  rw [hu2]
  rw [runSeq_append]
  rw [hu3]
  rw [runSeq_append]
  rw [hu4]
  rw [runSeq_append]
  rw [hu5]
  rw [runSeq_append]
  rw [hu6]
  rw [runSeq_append]
  rw [hu7]
  rw [hu8]
  -- u8 = copyLoopStep
  apply State.ext
  · simp only [u8, copyLoopStep, hptr]
  · funext i
    simp only [u8, u7, u6, u5, u4, u3, u2, u1, copyLoopStep]
    by_cases h1i : i = test
    · simp only [h1i, if_neg hsep.2.2.1, if_neg hsep.2.1, if_neg hsep.1, if_true]
    · by_cases h2i : i = s1
      · simp only [h2i, if_neg hsep.2.2.2.2.1, if_neg hsep.2.2.2.1,
          if_neg (Ne.symm hsep.1), if_true]
      · by_cases h3i : i = s2
        · simp only [h3i, if_neg hsep.2.2.2.2.2, if_neg (Ne.symm hsep.2.2.2.1),
            if_neg (Ne.symm hsep.2.1), if_true]
        · by_cases h4i : i = s4
          · simp only [h4i, if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
              if_neg (Ne.symm hsep.2.2.2.2.2), if_true]
          · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
  · rfl
  · rfl

/-- The copy loop moves the tested value into three cells: from a state with
    `test` holding `v` and `s1`/`s2`/`s4` holding `a`/`b`/`c`, it reaches a
    state with `test` holding `0` and `s1`/`s2`/`s4` holding `a+v`/`b+v`/`c+v`,
    leaving the pointer and every other cell unchanged. -/
theorem run_copyLoop (v : Nat) (test s1 s2 s4 : Int) (a b c : Nat) (s : State)
    (hptr : s.ptr = test) (hv : s.tape test = v) (h1 : s.tape s1 = a)
    (h2 : s.tape s2 = b) (h4 : s.tape s4 = c)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s4 ∧ s1 ≠ s2 ∧ s1 ≠ s4 ∧ s2 ≠ s4) :
    ∃ n : Nat, run n (copyLoop test s1 s2 s4) s = some (copyLoopPost test s1 s2 s4 a b c v s) := by
  induction v generalizing a b c s with
  | zero =>
      refine ⟨1, ?_⟩
      have hzero : s.currentVal = 0 := by
        simp only [State.currentVal, hptr, hv]
      have hstep : step (copyLoop test s1 s2 s4) s = some ([], s) := by
        simp only [copyLoop, step, if_pos hzero]
      simp only [run, hstep]
      congr 1
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
      rcases ih (a + 1) (b + 1) (c + 1) s' hs'ptr hs'test hs's1 hs's2 hs's4 with ⟨n, hn⟩
      refine ⟨1 + (copyLoopBody test s1 s2 s4).length + n, ?_⟩
      rw [show 1 + (copyLoopBody test s1 s2 s4).length + n =
        Nat.succ ((copyLoopBody test s1 s2 s4).length + n) by
        rw [Nat.succ_eq_add_one]
        ring]
      change run (Nat.succ ((copyLoopBody test s1 s2 s4).length + n))
        [.loop (copyLoopBody test s1 s2 s4)] s = some (copyLoopPost test s1 s2 s4 a b c (v + 1) s)
      simp only [run, step, if_neg hne]
      rw [List.append_nil]
      rw [run_append]
      · rw [hrunSeq]
        change run n (copyLoop test s1 s2 s4) s' = some (copyLoopPost test s1 s2 s4 a b c (v + 1) s)
        rw [hn]
        congr 1
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
      · exact loop_free_copyLoopBody test s1 s2 s4

end LeanBF
