/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Semantics
import LeanBF.Theory.BodyLoop
import LeanBF.Theory.IfZeroElse.Blocks

/-!
# ifZeroElse Setup

The shared setup prefix of `Compiler.ifZeroElse` reaches the `thenBodyState`
when the tested cell is zero and the `elseBodyState` when it is non-zero.

## Theorems

* `runsTo_setup_zero`: The setup reaches the `thenBodyState` when `test` is
  zero.
* `runsTo_setup_succ`: The setup reaches the `elseBodyState` when `test` is
  non-zero.
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

end LeanBF
