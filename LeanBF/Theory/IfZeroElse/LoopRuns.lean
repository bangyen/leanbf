/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Semantics
import LeanBF.Theory.BodyLoop

/-!
# Loop RunsTo Facts

The copy, flag, and restore loops in `RunsTo` form: the copy loop moves the
tested value into three cells, the flag loop computes whether a cell was
zero, and the restore loop moves a cell back.

## Theorems

* `runsTo_copyLoop`: The copy loop moves the tested value into three cells
  (RunsTo form).
* `runsTo_flagLoop`: The flag loop clears `s3` once per unit of `s1` (RunsTo
  form).
* `runsTo_restoreLoop`: The restore loop moves `s4` back into `test` (RunsTo
  form).
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

end LeanBF
