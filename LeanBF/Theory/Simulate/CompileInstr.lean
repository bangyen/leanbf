/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.Basics

/-!
# Compiled Instructions

The compiled `inc1`, `inc2`, and `halt` blocks: each runs from a window
state and updates the machine's cells and program counter.

## Theorems

* `runsTo_compileInstr_inc1`: The `inc1` block increments `c1` and sets the
  program counter.
* `runsTo_compileInstr_inc2`: The `inc2` block increments `c2` and sets the
  program counter.
* `runsTo_compileInstr_halt`: The `halt` block clears the running flag.
-/

namespace LeanBF

/-- The `inc1` block increments `c1` and sets the program counter. -/
theorem runsTo_compileInstr_inc1 (next : Nat) (ms : Minsky.State)
    (s : State)
    (hptr : s.ptr = 1) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.inc1 next), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 + 1 ∧
        s'.tape 3 = ms.c2 ∧ s'.tape 0 = 1 ∧
        s'.tape 4 = s.tape 4 ∧ s'.tape 5 = s.tape 5 ∧ s'.tape 6 = s.tape 6 ∧
        s'.tape 8 = s.tape 8 ∧ s'.tape 9 = s.tape 9 ∧ s'.tape 10 = s.tape 10 ∧
        s'.tape 12 = s.tape 12 := by
  let a1 : State := { s with ptr := 2 }
  let a2 : State := { a1 with tape := fun i => if i = (2 : Int) then ms.c1 + 1 else a1.tape i }
  let a3 : State := { a2 with ptr := 1 }
  let a4 : State := { a3 with tape := fun i => if i = (1 : Int) then next else a3.tape i }
  have h1 : RunsTo (Compiler.movePtr 1 2, s) a1 := by
    simpa only [a1] using runsTo_movePtr 1 2 s hptr
  have h2 : RunsTo ([.inc_val], a1) a2 := by
    have hinc : RunsTo ([.inc_val], a1)
        { a1 with tape := fun i => if i = a1.ptr then a1.tape a1.ptr + 1 else a1.tape i } :=
      runsTo_inc_val a1
    have heq : { a1 with tape := fun i => if i = a1.ptr then a1.tape a1.ptr + 1 else a1.tape i } =
        a2 := by
      apply State.ext
      · rfl
      · funext i
        simp only [a1, a2]
        by_cases hi : i = (2 : Int)
        · simp only [hi, if_true, hc1]
        · simp only [if_neg hi]
      · rfl
      · rfl
    rw [heq] at hinc
    exact hinc
  have ha2 : a2.ptr = 2 := by simp only [a2, a1]
  have h3 : RunsTo (Compiler.movePtr 2 1, a2) a3 := by
    simpa only [a3] using runsTo_movePtr 2 1 a2 ha2
  have ha3 : a3.ptr = 1 := by simp only [a3]
  have h4 : RunsTo (Compiler.setHere next, a3) a4 := by
    have hset : RunsTo (Compiler.setHere next, a3)
        { a3 with tape := fun i => if i = a3.ptr then next else a3.tape i } :=
      runsTo_setHere next a3
    have heq : { a3 with tape := fun i => if i = a3.ptr then next else a3.tape i } = a4 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (1 : Int)
        · simp only [hi, if_true, a4, a3]
        · simp only [if_neg hi, a4, a3]
      · rfl
      · rfl
    rw [heq] at hset
    exact hset
  have hchain : RunsTo (Compiler.compileInstr (.inc1 next), s) a4 := by
    simpa only [Compiler.compileInstr, List.append_assoc] using
      (RunsTo_append (Compiler.setHere next) a3 a4
        (RunsTo_append (Compiler.movePtr 2 1) a2 a3
          (RunsTo_append [.inc_val] a1 a2 h1 h2) h3)
        h4)
  refine ⟨a4, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [a4, a3, if_true]
  · simp only [a4, a3, a2, a1, hc1]
    norm_num
  · simp only [a4, a3, a2, a1, hc2]
    norm_num
  · simp only [a4, a3, a2, a1, hrun]
    norm_num
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (4 : Int) = 1), if_neg (by decide : ¬ (4 : Int) = 2)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (5 : Int) = 1), if_neg (by decide : ¬ (5 : Int) = 2)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (6 : Int) = 1), if_neg (by decide : ¬ (6 : Int) = 2)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (8 : Int) = 1), if_neg (by decide : ¬ (8 : Int) = 2)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (9 : Int) = 1), if_neg (by decide : ¬ (9 : Int) = 2)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (10 : Int) = 1), if_neg (by decide : ¬ (10 : Int) = 2)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (12 : Int) = 1), if_neg (by decide : ¬ (12 : Int) = 2)]

/-- The `inc2` block increments `c2` and sets the program counter. -/
theorem runsTo_compileInstr_inc2 (next : Nat) (ms : Minsky.State) (s : State)
    (hptr : s.ptr = 1) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.inc2 next), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 ∧
        s'.tape 3 = ms.c2 + 1 ∧ s'.tape 0 = 1 ∧
        s'.tape 4 = s.tape 4 ∧ s'.tape 5 = s.tape 5 ∧ s'.tape 6 = s.tape 6 ∧
        s'.tape 8 = s.tape 8 ∧ s'.tape 9 = s.tape 9 ∧ s'.tape 10 = s.tape 10 ∧
        s'.tape 12 = s.tape 12 := by
  let a1 : State := { s with ptr := 3 }
  let a2 : State := { a1 with tape := fun i => if i = (3 : Int) then ms.c2 + 1 else a1.tape i }
  let a3 : State := { a2 with ptr := 1 }
  let a4 : State := { a3 with tape := fun i => if i = (1 : Int) then next else a3.tape i }
  have h1 : RunsTo (Compiler.movePtr 1 3, s) a1 := by
    simpa only [a1] using runsTo_movePtr 1 3 s hptr
  have h2 : RunsTo ([.inc_val], a1) a2 := by
    have hinc : RunsTo ([.inc_val], a1)
        { a1 with tape := fun i => if i = a1.ptr then a1.tape a1.ptr + 1 else a1.tape i } :=
      runsTo_inc_val a1
    have heq : { a1 with tape := fun i => if i = a1.ptr then a1.tape a1.ptr + 1 else a1.tape i } =
        a2 := by
      apply State.ext
      · rfl
      · funext i
        simp only [a1, a2]
        by_cases hi : i = (3 : Int)
        · simp only [hi, if_true, hc2]
        · simp only [if_neg hi]
      · rfl
      · rfl
    rw [heq] at hinc
    exact hinc
  have ha2 : a2.ptr = 3 := by simp only [a2, a1]
  have h3 : RunsTo (Compiler.movePtr 3 1, a2) a3 := by
    simpa only [a3] using runsTo_movePtr 3 1 a2 ha2
  have ha3 : a3.ptr = 1 := by simp only [a3]
  have h4 : RunsTo (Compiler.setHere next, a3) a4 := by
    have hset : RunsTo (Compiler.setHere next, a3)
        { a3 with tape := fun i => if i = a3.ptr then next else a3.tape i } :=
      runsTo_setHere next a3
    have heq : { a3 with tape := fun i => if i = a3.ptr then next else a3.tape i } = a4 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (1 : Int)
        · simp only [hi, if_true, a4, a3]
        · simp only [if_neg hi, a4, a3]
      · rfl
      · rfl
    rw [heq] at hset
    exact hset
  have hchain : RunsTo (Compiler.compileInstr (.inc2 next), s) a4 := by
    simpa only [Compiler.compileInstr, List.append_assoc] using
      (RunsTo_append (Compiler.setHere next) a3 a4
        (RunsTo_append (Compiler.movePtr 3 1) a2 a3
          (RunsTo_append [.inc_val] a1 a2 h1 h2) h3)
        h4)
  refine ⟨a4, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [a4, a3, if_true]
  · simp only [a4, a3, a2, a1, hc1]
    rw [if_neg (by decide : ¬ (2 : Int) = 1), if_neg (by decide : ¬ (2 : Int) = 3)]
  · simp only [a4, a3, a2, a1, hc2]
    rw [if_neg (by decide : ¬ (3 : Int) = 1), if_true]
  · simp only [a4, a3, a2, a1, hrun]
    rw [if_neg (by decide : ¬ (0 : Int) = 1), if_neg (by decide : ¬ (0 : Int) = 3)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (4 : Int) = 1), if_neg (by decide : ¬ (4 : Int) = 3)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (5 : Int) = 1), if_neg (by decide : ¬ (5 : Int) = 3)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (6 : Int) = 1), if_neg (by decide : ¬ (6 : Int) = 3)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (8 : Int) = 1), if_neg (by decide : ¬ (8 : Int) = 3)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (9 : Int) = 1), if_neg (by decide : ¬ (9 : Int) = 3)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (10 : Int) = 1), if_neg (by decide : ¬ (10 : Int) = 3)]
  · simp only [a4, a3, a2, a1]
    rw [if_neg (by decide : ¬ (12 : Int) = 1), if_neg (by decide : ¬ (12 : Int) = 3)]

/-- The `halt` block clears the running flag. -/
theorem runsTo_compileInstr_halt (s : State) (hptr : s.ptr = 1)
    (hpc : s.tape 1 = 0) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr .halt, s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = 0 ∧ s'.tape 0 = 0 ∧
        s'.tape 2 = s.tape 2 ∧ s'.tape 3 = s.tape 3 ∧
        s'.tape 4 = s.tape 4 ∧ s'.tape 5 = s.tape 5 ∧ s'.tape 6 = s.tape 6 ∧
        s'.tape 8 = s.tape 8 ∧ s'.tape 9 = s.tape 9 ∧ s'.tape 10 = s.tape 10 ∧
        s'.tape 12 = s.tape 12 := by
  let a1 : State := { s with ptr := 0 }
  let a2 : State := { a1 with tape := fun i => if i = (0 : Int) then 0 else a1.tape i }
  let a3 : State := { a2 with ptr := 1 }
  have h1 : RunsTo (Compiler.movePtr 1 0, s) a1 := by
    simpa only [a1] using runsTo_movePtr 1 0 s hptr
  have h2 : RunsTo (Compiler.clearHere, a1) a2 := by
    have hc : RunsTo (Compiler.clearHere, a1)
        { a1 with tape := fun i => if i = a1.ptr then 0 else a1.tape i } :=
      runsTo_clearHere (a1.tape a1.ptr) a1 rfl
    have heq : { a1 with tape := fun i => if i = a1.ptr then 0 else a1.tape i } = a2 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (0 : Int)
        · simp only [hi, if_true, a2, a1]
        · simp only [if_neg hi, a2, a1]
      · rfl
      · rfl
    rw [heq] at hc
    exact hc
  have ha2 : a2.ptr = 0 := by simp only [a2, a1]
  have h3 : RunsTo (Compiler.movePtr 0 1, a2) a3 := by
    simpa only [a3] using runsTo_movePtr 0 1 a2 ha2
  have hchain : RunsTo (Compiler.compileInstr .halt, s) a3 := by
    simpa only [Compiler.compileInstr, List.append_assoc] using
      (RunsTo_append (Compiler.movePtr 0 1) a2 a3
        (RunsTo_append (Compiler.clearHere) a1 a2 h1 h2) h3)
  refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (1 : Int) = 0)]
    exact hpc
  · simp only [a3, a2, a1, hrun]
    rw [if_true]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (2 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (3 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (4 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (5 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (6 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (8 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (9 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (10 : Int) = 0)]
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (12 : Int) = 0)]

end LeanBF
