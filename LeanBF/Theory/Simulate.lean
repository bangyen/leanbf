/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.IfZeroElse

/-!
# The Dispatch Simulation

This module wires `Compiler.compileInstr` and `Compiler.compileProgram` into
the simulation machinery, proving that the compiled dispatch loop simulates a
Minsky machine step by step. Together with `Theory.Completeness`, this yields
the `turingCompleteness` statement.

## Main definitions

* `SimulatesAt`: A Brainfuck state that simulates a Minsky state with the
  pointer at a given cell.

## Theorems

* `runSeq_replicate_inc_val`: Incrementing the current cell `n` times adds
  `n`.
* `runsTo_setHere`: `setHere n` sets the current cell to `n`.
* `runsTo_inc_val`: A single `+` increments the current cell.
* `runsTo_jzdecThen`: The `jzdec` zero branch sets the program counter.
* `runsTo_jzdecElse`: The `jzdec` non-zero branch decrements the tested cell
  and sets the program counter.
* `runsTo_compileInstr_inc1`: The `inc1` block increments `c1` and sets the
  program counter.
* `runsTo_compileInstr_inc2`: The `inc2` block increments `c2` and sets the
  program counter.
* `runsTo_compileInstr_jzdec1`: The `jzdec1` block branches on `c1`.
* `runsTo_compileInstr_jzdec2`: The `jzdec2` block branches on `c2`.
* `runsTo_compileInstr_halt`: The `halt` block clears the running flag.
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
    (hptr : s.ptr = 1) (_hpc : s.tape 1 = 0) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.inc1 next), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 + 1 ∧
        s'.tape 3 = ms.c2 ∧ s'.tape 0 = 1 := by
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
  refine ⟨a4, hchain, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [a4, a3, if_true]
  · simp only [a4, a3, a2, a1, hc1]
    norm_num
  · simp only [a4, a3, a2, a1, hc2]
    norm_num
  · simp only [a4, a3, a2, a1, hrun]
    norm_num

/-- The `inc2` block increments `c2` and sets the program counter. -/
theorem runsTo_compileInstr_inc2 (next : Nat) (ms : Minsky.State) (s : State)
    (hptr : s.ptr = 1) (_hpc : s.tape 1 = 0) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.inc2 next), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 ∧
        s'.tape 3 = ms.c2 + 1 ∧ s'.tape 0 = 1 := by
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
  refine ⟨a4, hchain, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [a4, a3, if_true]
  · simp only [a4, a3, a2, a1, hc1]
    rw [if_neg (by decide : ¬ (2 : Int) = 1), if_neg (by decide : ¬ (2 : Int) = 3)]
  · simp only [a4, a3, a2, a1, hc2]
    rw [if_neg (by decide : ¬ (3 : Int) = 1), if_true]
  · simp only [a4, a3, a2, a1, hrun]
    rw [if_neg (by decide : ¬ (0 : Int) = 1), if_neg (by decide : ¬ (0 : Int) = 3)]

/-- The `halt` block clears the running flag. -/
theorem runsTo_compileInstr_halt (s : State) (hptr : s.ptr = 1)
    (hpc : s.tape 1 = 0) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr .halt, s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = 0 ∧ s'.tape 0 = 0 := by
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
  refine ⟨a3, hchain, ?_, ?_, ?_⟩
  · rfl
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (1 : Int) = 0)]
    exact hpc
  · simp only [a3, a2, a1, hrun]
    rw [if_true]

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

/-- The `jzdec1` block branches on `c1`. -/
theorem runsTo_compileInstr_jzdec2 (ifZero ifNonZero : Nat) (ms : Minsky.State)
    (s : State)
    (hptr : s.ptr = 1) (_hpc : s.tape 1 = 0) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.jzdec2 ifZero ifNonZero), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = (if ms.c2 = 0 then ifZero else ifNonZero) ∧
        s'.tape 2 = ms.c1 ∧
        s'.tape 3 = (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) ∧ s'.tape 0 = 1 := by
  let a1 : State := { s with ptr := 3 }
  have h1 : RunsTo (Compiler.movePtr 1 3, s) a1 := by
    simpa only [a1] using runsTo_movePtr 1 3 s hptr
  have ha1ptr : a1.ptr = 3 := by simp only [a1]
  have ha1tape2 : a1.tape 2 = ms.c1 := by simp only [a1, hc1]
  have ha1tape3 : a1.tape 3 = ms.c2 := by simp only [a1, hc2]
  have ha1run : a1.tape 0 = 1 := by simp only [a1, hrun]
  let thenBody : Program := Compiler.movePtr 3 1 ++ Compiler.setHere ifZero ++ Compiler.movePtr 1 3
  let elseBody : Program :=
    [.dec_val] ++ Compiler.movePtr 3 1 ++ Compiler.setHere ifNonZero ++ Compiler.movePtr 1 3
  by_cases hzero : ms.c2 = 0
  · have ht0 : a1.tape 3 = 0 := by
      rw [ha1tape3]
      exact hzero
    let s_then : State :=
      { thenBodyState 3 13 14 15 16 a1 with
        tape := fun i =>
          if i = (1 : Int) then ifZero else (thenBodyState 3 13 14 15 16 a1).tape i }
    have hthen : RunsTo (thenBody, thenBodyState 3 13 14 15 16 a1) s_then := by
      have hr : RunsTo (Compiler.movePtr 3 1 ++ Compiler.setHere ifZero ++
          Compiler.movePtr 1 3, thenBodyState 3 13 14 15 16 a1)
          { thenBodyState 3 13 14 15 16 a1 with
            tape := fun i =>
              if i = (1 : Int) then ifZero else (thenBodyState 3 13 14 15 16 a1).tape i } :=
        runsTo_jzdecThen (3 : Int) ifZero (thenBodyState 3 13 14 15 16 a1)
          (by simp only [thenBodyState])
      simpa only [thenBody, s_then] using hr
    have h1t : s_then.ptr = 3 := by simp only [s_then, thenBodyState]
    have h2t : s_then.tape 13 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (13 : Int) = 1)]
      rw [if_neg (by decide : ¬ (13 : Int) = 3)]
      rw [if_true]
    have h3t : s_then.tape 14 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (14 : Int) = 1)]
      rw [if_neg (by decide : ¬ (14 : Int) = 3)]
      rw [if_neg (by decide : ¬ (14 : Int) = 13)]
      rw [if_true]
    have h4t : s_then.tape 16 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (16 : Int) = 1)]
      rw [if_neg (by decide : ¬ (16 : Int) = 3)]
      rw [if_neg (by decide : ¬ (16 : Int) = 13)]
      rw [if_neg (by decide : ¬ (16 : Int) = 14)]
      rw [if_neg (by decide : ¬ (16 : Int) = 15)]
      rw [if_true]
    have hif : RunsTo (Compiler.ifZeroElse 3 13 14 15 16 thenBody elseBody, a1)
        (ifZeroElsePost 3 13 14 15 16 s_then) :=
      runsTo_ifZeroElse_zero 3 13 14 15 16 thenBody elseBody a1 s_then ha1ptr ht0
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ hthen h1t h2t h3t h4t
    let a2 : State := ifZeroElsePost 3 13 14 15 16 s_then
    have ha2ptr : a2.ptr = 3 := by
      simp only [a2, ifZeroElsePost]
    have ha2tape1 : a2.tape 1 = ifZero := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (1 : Int) = 13)]
      rw [if_neg (by decide : ¬ (1 : Int) = 14)]
      rw [if_neg (by decide : ¬ (1 : Int) = 15)]
      rw [if_neg (by decide : ¬ (1 : Int) = 16)]
      rw [if_true]
    have ha2tape2 : a2.tape 2 = ms.c1 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (2 : Int) = 13)]
      rw [if_neg (by decide : ¬ (2 : Int) = 14)]
      rw [if_neg (by decide : ¬ (2 : Int) = 15)]
      rw [if_neg (by decide : ¬ (2 : Int) = 16)]
      rw [if_neg (by decide : ¬ (2 : Int) = 1)]
      simp only [thenBodyState]
      rw [if_neg (by decide : ¬ (2 : Int) = 3)]
      exact ha1tape2
    have ha2tape3 : a2.tape 3 = ms.c2 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (3 : Int) = 13)]
      rw [if_neg (by decide : ¬ (3 : Int) = 14)]
      rw [if_neg (by decide : ¬ (3 : Int) = 15)]
      rw [if_neg (by decide : ¬ (3 : Int) = 16)]
      rw [if_neg (by decide : ¬ (3 : Int) = 1)]
      simp only [thenBodyState]
      exact hzero.symm
    have ha2run : a2.tape 0 = 1 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (0 : Int) = 13)]
      rw [if_neg (by decide : ¬ (0 : Int) = 14)]
      rw [if_neg (by decide : ¬ (0 : Int) = 15)]
      rw [if_neg (by decide : ¬ (0 : Int) = 16)]
      rw [if_neg (by decide : ¬ (0 : Int) = 1)]
      simp only [thenBodyState]
      rw [if_neg (by decide : ¬ (0 : Int) = 3)]
      exact ha1run
    let a3 : State := { a2 with ptr := 1 }
    have h3 : RunsTo (Compiler.movePtr 3 1, a2) a3 := by
      simpa only [a3] using runsTo_movePtr 3 1 a2 ha2ptr
    have hchain : RunsTo (Compiler.compileInstr (.jzdec2 ifZero ifNonZero), s) a3 := by
      simpa only [Compiler.compileInstr, thenBody, elseBody, List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 3 1) a2 a3
          (RunsTo_append (Compiler.ifZeroElse 3 13 14 15 16 thenBody elseBody) a1 a2 h1 hif) h3)
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_true]
    · simp only [a3, ha2tape2]
    · simp only [a3, ha2tape3, hzero, if_true]
    · simp only [a3, ha2run]
  · have hw : ms.c2 = (ms.c2 - 1) + 1 := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero))]
    let w : Nat := ms.c2 - 1
    let s_else : State :=
      { elseBodyState 3 13 14 15 16 ms.c2 a1 with
        tape := fun i =>
          if i = (3 : Int) then (elseBodyState 3 13 14 15 16 ms.c2 a1).tape 3 - 1 else
          if i = (1 : Int) then ifNonZero else (elseBodyState 3 13 14 15 16 ms.c2 a1).tape i }
    have helse : RunsTo (elseBody, elseBodyState 3 13 14 15 16 ms.c2 a1) s_else := by
      have hr : RunsTo ([.dec_val] ++ Compiler.movePtr 3 1 ++ Compiler.setHere ifNonZero ++
          Compiler.movePtr 1 3, elseBodyState 3 13 14 15 16 ms.c2 a1)
          { elseBodyState 3 13 14 15 16 ms.c2 a1 with
            tape := fun i =>
              if i = (3 : Int) then (elseBodyState 3 13 14 15 16 ms.c2 a1).tape 3 - 1 else
              if i = (1 : Int) then ifNonZero else
                (elseBodyState 3 13 14 15 16 ms.c2 a1).tape i } :=
        runsTo_jzdecElse (3 : Int) ifNonZero (elseBodyState 3 13 14 15 16 ms.c2 a1)
          (by simp only [elseBodyState]) (by decide : ¬ (3 : Int) = 1)
      simpa only [elseBody, s_else] using hr
    have h1e : s_else.ptr = 3 := by simp only [s_else, elseBodyState]
    have h2e : s_else.tape 13 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (13 : Int) = 3)]
      rw [if_neg (by decide : ¬ (13 : Int) = 1)]
      rw [if_neg (by decide : ¬ (13 : Int) = 3)]
      rw [if_true]
    have h3e : s_else.tape 15 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (15 : Int) = 3)]
      rw [if_neg (by decide : ¬ (15 : Int) = 1)]
      rw [if_neg (by decide : ¬ (15 : Int) = 13)]
      rw [if_neg (by decide : ¬ (15 : Int) = 14)]
      rw [if_neg (by decide : ¬ (15 : Int) = 3)]
      rw [if_true]
    have h4e : s_else.tape 16 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (16 : Int) = 3)]
      rw [if_neg (by decide : ¬ (16 : Int) = 1)]
      rw [if_neg (by decide : ¬ (16 : Int) = 13)]
      rw [if_neg (by decide : ¬ (16 : Int) = 14)]
      rw [if_neg (by decide : ¬ (16 : Int) = 15)]
      rw [if_neg (by decide : ¬ (16 : Int) = 3)]
      rw [if_true]
    have helse' : RunsTo (elseBody, elseBodyState 3 13 14 15 16 (w + 1) a1) s_else := by
      rw [show ms.c2 = (ms.c2 - 1) + 1 from hw] at helse
      exact helse
    have hif : RunsTo (Compiler.ifZeroElse 3 13 14 15 16 thenBody elseBody, a1)
        (ifZeroElsePost 3 13 14 15 16 s_else) :=
      runsTo_ifZeroElse_succ w 3 13 14 15 16 thenBody elseBody a1 s_else ha1ptr
        (ha1tape3.trans hw)
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ helse' h1e h2e h3e h4e
    let a2 : State := ifZeroElsePost 3 13 14 15 16 s_else
    have ha2ptr : a2.ptr = 3 := by
      simp only [a2, ifZeroElsePost]
    have ha2tape1 : a2.tape 1 = ifNonZero := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (1 : Int) = 13)]
      rw [if_neg (by decide : ¬ (1 : Int) = 14)]
      rw [if_neg (by decide : ¬ (1 : Int) = 15)]
      rw [if_neg (by decide : ¬ (1 : Int) = 16)]
      rw [if_neg (by decide : ¬ (1 : Int) = 3)]
      rw [if_true]
    have ha2tape2 : a2.tape 2 = ms.c1 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (2 : Int) = 13)]
      rw [if_neg (by decide : ¬ (2 : Int) = 14)]
      rw [if_neg (by decide : ¬ (2 : Int) = 15)]
      rw [if_neg (by decide : ¬ (2 : Int) = 16)]
      rw [if_neg (by decide : ¬ (2 : Int) = 1)]
      simp only [elseBodyState]
      rw [if_neg (by decide : ¬ (2 : Int) = 3)]
      exact ha1tape2
    have ha2tape3 : a2.tape 3 = ms.c2 - 1 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (3 : Int) = 13)]
      rw [if_neg (by decide : ¬ (3 : Int) = 14)]
      rw [if_neg (by decide : ¬ (3 : Int) = 15)]
      rw [if_neg (by decide : ¬ (3 : Int) = 16)]
      rw [if_neg (by decide : ¬ (3 : Int) = 1)]
      rw [if_true]
      simp only [elseBodyState, if_true]
    have ha2run : a2.tape 0 = 1 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (0 : Int) = 13)]
      rw [if_neg (by decide : ¬ (0 : Int) = 14)]
      rw [if_neg (by decide : ¬ (0 : Int) = 15)]
      rw [if_neg (by decide : ¬ (0 : Int) = 16)]
      rw [if_neg (by decide : ¬ (0 : Int) = 1)]
      simp only [elseBodyState]
      rw [if_neg (by decide : ¬ (0 : Int) = 3)]
      exact ha1run
    let a3 : State := { a2 with ptr := 1 }
    have h3 : RunsTo (Compiler.movePtr 3 1, a2) a3 := by
      simpa only [a3] using runsTo_movePtr 3 1 a2 ha2ptr
    have hchain : RunsTo (Compiler.compileInstr (.jzdec2 ifZero ifNonZero), s) a3 := by
      simpa only [Compiler.compileInstr, thenBody, elseBody, List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 3 1) a2 a3
          (RunsTo_append (Compiler.ifZeroElse 3 13 14 15 16 thenBody elseBody) a1 a2 h1 hif) h3)
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_false]
    · simp only [a3, ha2tape2]
    · simp only [a3, ha2tape3, hzero, if_false]
    · simp only [a3, ha2run]

end LeanBF
