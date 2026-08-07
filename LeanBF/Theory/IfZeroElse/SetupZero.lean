/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.BodyLoop
import LeanBF.Theory.IfZeroElse.Blocks
import LeanBF.Theory.IfZeroElse.LoopRuns

/-!
# ifZeroElse Setup: Zero

The shared setup prefix of `Compiler.ifZeroElse` reaches the `thenBodyState`
when the tested cell is zero.

## Theorems

* `runsTo_setup_zero`: The setup reaches the `thenBodyState` when `test` is
  zero.
-/

namespace LeanBF


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

end LeanBF
