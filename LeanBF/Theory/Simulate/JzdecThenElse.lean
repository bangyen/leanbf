/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.Basics
import LeanBF.Theory.Simulate.CompileInstr

/-!
# Jzdec Branches

The two branches of a `jzdec` block: the zero branch sets the `ifZero`
program counter, and the non-zero branch decrements the counter and sets the
`ifNonZero` program counter.

## Theorems

* `runsTo_jzdecThen`: The `jzdec` zero branch sets the `ifZero` program
  counter.
* `runsTo_jzdecElse`: The `jzdec` non-zero branch decrements the counter and
  sets the `ifNonZero` program counter.
-/

namespace LeanBF

/-- The `jzdec` zero branch: set the program counter and return to the tested
    cell. -/
theorem runsTo_jzdecThen (testCell : Int) (ifZero : Nat) (s : State)
    (hptr : s.ptr = testCell) :
    RunsTo (Compiler.movePtr testCell 1 ++
        Compiler.setHere ifZero ++ Compiler.movePtr 1 testCell, s)
      { s with ptr := testCell, tape := fun i => if i = (1 : Int) then ifZero else s.tape i } := by
  let a1 : State := { s with ptr := 1 }
  let a2 : State := { a1 with tape := fun i => if i = (1 : Int) then ifZero else a1.tape i }
  let a3 : State := { a2 with ptr := testCell }
  have h1 : RunsTo (Compiler.movePtr testCell 1, s) a1 := by
    simpa only [a1] using runsTo_movePtr testCell 1 s hptr
  have h2 : RunsTo (Compiler.setHere ifZero, a1) a2 := by
    have hset : RunsTo (Compiler.setHere ifZero, a1)
        { a1 with tape := fun i => if i = a1.ptr then ifZero else a1.tape i } :=
      runsTo_setHere ifZero a1
    have heq : { a1 with tape := fun i => if i = a1.ptr then ifZero else a1.tape i } = a2 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (1 : Int)
        · simp only [hi, if_true, a2, a1]
        · simp only [if_neg hi, a2, a1]
      · rfl
      · rfl
    rw [heq] at hset
    exact hset
  have ha2 : a2.ptr = 1 := by simp only [a2, a1]
  have h3 : RunsTo (Compiler.movePtr 1 testCell, a2) a3 := by
    simpa only [a3] using runsTo_movePtr 1 testCell a2 ha2
  have hchain : RunsTo (Compiler.movePtr testCell 1 ++ Compiler.setHere ifZero ++
      Compiler.movePtr 1 testCell, s) a3 :=
    RunsTo_append (Compiler.movePtr 1 testCell) a2 a3
      (RunsTo_append (Compiler.setHere ifZero) a1 a2 h1 h2) h3
  have heq : a3 =
      { s with ptr := testCell, tape := fun i => if i = (1 : Int) then ifZero else s.tape i } := by
    apply State.ext
    · rfl
    · funext i
      by_cases hi : i = (1 : Int)
      · simp only [hi, if_true, a3, a2, a1]
      · simp only [if_neg hi, a3, a2, a1]
    · rfl
    · rfl
  rw [heq] at hchain
  exact hchain

/-- The `jzdec` non-zero branch: decrement the tested cell, set the program
    counter, and return to the tested cell. -/
theorem runsTo_jzdecElse (testCell : Int) (ifNonZero : Nat) (s : State)
    (hptr : s.ptr = testCell) (hne : testCell ≠ 1) :
    RunsTo ([.dec_val] ++ Compiler.movePtr testCell 1 ++ Compiler.setHere ifNonZero ++
        Compiler.movePtr 1 testCell, s)
      { s with ptr := testCell, tape := fun i => if i = testCell then s.tape testCell - 1 else
        if i = (1 : Int) then ifNonZero else s.tape i } := by
  let a1 : State := { s with tape := fun i =>
      if i = testCell then s.tape testCell - 1 else s.tape i }
  let a2 : State := { a1 with ptr := 1 }
  let a3 : State := { a2 with tape := fun i => if i = (1 : Int) then ifNonZero else a2.tape i }
  let a4 : State := { a3 with ptr := testCell }
  have h1 : RunsTo ([.dec_val], s) a1 := by
    have hdec : RunsTo ([.dec_val], s)
        { s with tape := fun i => if i = s.ptr then s.tape s.ptr - 1 else s.tape i } := by
      have hstep : step [.dec_val] s = some ([], s.decVal) := by simp only [step]
      have heq : s.decVal =
          { s with tape := fun i => if i = s.ptr then s.tape s.ptr - 1 else s.tape i } := by
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = s.ptr
          · simp only [hi, if_true, State.decVal, State.modifyCell]
          · simp only [if_neg hi, State.decVal, State.modifyCell]
        · rfl
        · rfl
      rw [← heq]
      exact RunsTo.step [.dec_val] s s.decVal [] s.decVal hstep (RunsTo.halt s.decVal)
    have heq2 : { s with tape := fun i => if i = s.ptr then s.tape s.ptr - 1 else s.tape i }
        = a1 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = testCell
        · simp only [hi, if_true, a1, hptr]
        · simp only [if_neg hi, a1, hptr]
      · rfl
      · rfl
    rw [heq2] at hdec
    exact hdec
  have ha1 : a1.ptr = testCell := by simp only [a1, hptr]
  have h2 : RunsTo (Compiler.movePtr testCell 1, a1) a2 := by
    simpa only [a2] using runsTo_movePtr testCell 1 a1 ha1
  have h3 : RunsTo (Compiler.setHere ifNonZero, a2) a3 := by
    have hset : RunsTo (Compiler.setHere ifNonZero, a2)
        { a2 with tape := fun i => if i = a2.ptr then ifNonZero else a2.tape i } :=
      runsTo_setHere ifNonZero a2
    have heq : { a2 with tape := fun i => if i = a2.ptr then ifNonZero else a2.tape i } = a3 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (1 : Int)
        · simp only [hi, if_true, a3, a2]
        · simp only [if_neg hi, a3, a2]
      · rfl
      · rfl
    rw [heq] at hset
    exact hset
  have ha3 : a3.ptr = 1 := by simp only [a3, a2]
  have h4 : RunsTo (Compiler.movePtr 1 testCell, a3) a4 := by
    simpa only [a4] using runsTo_movePtr 1 testCell a3 ha3
  have hchain : RunsTo ([.dec_val] ++ Compiler.movePtr testCell 1 ++ Compiler.setHere ifNonZero ++
      Compiler.movePtr 1 testCell, s) a4 :=
    RunsTo_append (Compiler.movePtr 1 testCell) a3 a4
      (RunsTo_append (Compiler.setHere ifNonZero) a2 a3
        (RunsTo_append (Compiler.movePtr testCell 1) a1 a2 h1 h2) h3)
      h4
  have heq : a4 =
      { s with ptr := testCell, tape := fun i => if i = testCell then s.tape testCell - 1 else
        if i = (1 : Int) then ifNonZero else s.tape i } := by
    apply State.ext
    · rfl
    · funext i
      simp only [a4, a3, a2, a1]
      by_cases h1i : i = testCell
      · simp only [h1i, if_true]
        rw [if_neg hne]
      · by_cases h2i : i = (1 : Int)
        · simp only [h2i, if_true]
          rw [if_neg (Ne.symm hne)]
        · simp only [if_neg h1i, if_neg h2i]
    · rfl
    · rfl
  rw [heq] at hchain
  exact hchain

end LeanBF
