/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse

/-!
# Compiled Instructions

`SimulatesAt`, the basic cell-write blocks, and the compiled `inc1`, `inc2`,
`halt`, and `jzdec`-branch blocks: each runs from a window state and updates
the machine's cells and program counter.

## Main definitions

* `SimulatesAt`: A Brainfuck state that simulates a Minsky state with the
  pointer at cell `p`.

## Theorems

* `runSeq_replicate_inc_val`: Incrementing the current cell n times adds n to
  it.
* `runsTo_setHere`: Setting the current cell to `n` writes `n`.
* `runsTo_inc_val`: A single `+` increments the current cell.
* `runsTo_compileInstr_inc1`: The `inc1` block increments `c1` and sets the
  program counter.
* `runsTo_compileInstr_inc2`: The `inc2` block increments `c2` and sets the
  program counter.
* `runsTo_compileInstr_halt`: The `halt` block clears the running flag.
* `runsTo_jzdecThen`: The jzdec zero branch sets the ifZero program counter.
* `runsTo_jzdecElse`: The jzdec non-zero branch decrements the counter and
  sets the ifNonZero program counter.
-/

namespace LeanBF

/-- A Brainfuck state that simulates a Minsky state with the pointer at cell
    `p`. The running flag (cell `0`) is set, and cells 1-3 hold `pc`, `c1`,
    `c2`. -/
def SimulatesAt (ms : Minsky.State) (p : Int) (bfs : State) : Prop :=
  bfs.ptr = p ∧ bfs.tape 1 = ms.pc ∧ bfs.tape 2 = ms.c1 ∧
    bfs.tape 3 = ms.c2 ∧ bfs.tape 0 = 1

/-- Incrementing the current cell `n` times adds `n` to it, without moving
    the pointer or changing the I/O. -/
theorem runSeq_replicate_inc_val (n : Nat) : ∀ (s : State),
    runSeq (List.replicate n .inc_val) s =
      { s with tape := fun i => if i = s.ptr then s.tape s.ptr + n else s.tape i } := by
  induction n with
  | zero =>
      intro s
      simp only [List.replicate, runSeq]
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = s.ptr
        · simp only [hi, if_true, Nat.add_zero]
        · simp only [if_neg hi]
      · rfl
      · rfl
  | succ n ih =>
      intro s
      rw [List.replicate_succ]
      simp only [runSeq, stepOne]
      rw [ih (s.incVal)]
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = s.ptr
        · simp only [hi, if_true, State.incVal, State.modifyCell]
          ring
        · simp only [if_neg hi, State.incVal, State.modifyCell]
      · rfl
      · rfl

/-- `setHere n` sets the current cell to `n` without moving the pointer. -/
theorem runsTo_setHere (n : Nat) (s : State) :
    RunsTo (Compiler.setHere n, s)
      { s with tape := fun i => if i = s.ptr then n else s.tape i } := by
  let c : State := { s with tape := fun i => if i = s.ptr then 0 else s.tape i }
  have hcptr : c.ptr = s.ptr := by simp only [c]
  have hcval : c.tape c.ptr = 0 := by
    simp only [c]
    rw [if_true]
  have h1 : RunsTo (Compiler.clearHere, s) c := by
    have hc : RunsTo (Compiler.clearHere, s)
        { s with tape := fun i => if i = s.ptr then 0 else s.tape i } :=
      runsTo_clearHere (s.tape s.ptr) s rfl
    simpa only [c] using hc
  have hl : LoopFree (List.replicate n .inc_val) :=
    loop_free_replicate n .inc_val (by intro body h'; cases h')
  have h2 : RunsTo (List.replicate n .inc_val, c)
      { c with tape := fun i => if i = c.ptr then n else c.tape i } := by
    have hb : RunsTo (List.replicate n .inc_val, c) (runSeq (List.replicate n .inc_val) c) :=
      runsTo_of_loopFree (List.replicate n .inc_val) c hl
    have hs : runSeq (List.replicate n .inc_val) c =
        { c with tape := fun i => if i = c.ptr then n else c.tape i } := by
      rw [runSeq_replicate_inc_val n c]
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = c.ptr
        · simp only [hi, if_true, hcval, Nat.zero_add]
        · simp only [if_neg hi, c]
      · rfl
      · rfl
    rw [hs] at hb
    exact hb
  have hchain : RunsTo (Compiler.setHere n, s)
      { c with tape := fun i => if i = c.ptr then n else c.tape i } :=
    RunsTo_append (List.replicate n .inc_val) c
      { c with tape := fun i => if i = c.ptr then n else c.tape i } h1 h2
  have heq : { c with tape := fun i => if i = c.ptr then n else c.tape i } =
      { s with tape := fun i => if i = s.ptr then n else s.tape i } := by
    apply State.ext
    · rfl
    · funext i
      by_cases hi : i = s.ptr
      · simp only [hi, if_true, c]
      · simp only [if_neg hi, c]
    · rfl
    · rfl
  rw [heq] at hchain
  exact hchain

/-- A single `+` increments the current cell. -/
theorem runsTo_inc_val (s : State) :
    RunsTo ([.inc_val], s)
      { s with tape := fun i => if i = s.ptr then s.tape s.ptr + 1 else s.tape i } := by
  have hstep : step [.inc_val] s = some ([], s.incVal) := by simp only [step]
  have heq : s.incVal =
      { s with tape := fun i => if i = s.ptr then s.tape s.ptr + 1 else s.tape i } := by
    apply State.ext
    · rfl
    · funext i
      by_cases hi : i = s.ptr
      · simp only [hi, if_true, State.incVal, State.modifyCell]
      · simp only [if_neg hi, State.incVal, State.modifyCell]
    · rfl
    · rfl
  rw [← heq]
  exact RunsTo.step [.inc_val] s s.incVal [] s.incVal hstep (RunsTo.halt s.incVal)

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
