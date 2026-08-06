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
* `windowBlockStart`: The state in which a window runs its block.
* `runsTo_dec_val`: A single `-` decrements the current cell.
* `runsTo_window_match`: A window with a zero `pc` runs its block once and
  sets the `done` flag.
* `windowBlockStart_tape`: The prepared window state's cells.
* `runsTo_window_skip`: A window with a non-zero `pc` decrements it.
* `runsTo_window_inc1`: The `inc1` window.
* `runsTo_window_inc2`: The `inc2` window.
* `runsTo_window_jzdec1`: The `jzdec1` window.
* `runsTo_window_jzdec2`: The `jzdec2` window.
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
    (hptr : s.ptr = 1) (_hpc : s.tape 1 = 0) (hc1 : s.tape 2 = ms.c1)
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
  refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [a3, a2, a1]
    rw [if_neg (by decide : ¬ (1 : Int) = 0)]
    exact hpc
  · simp only [a3, a2, a1, hrun]
    rw [if_true]
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

/-- The `jzdec1` block branches on `c1`. -/
theorem runsTo_compileInstr_jzdec1 (ifZero ifNonZero : Nat) (ms : Minsky.State) (s : State)
    (hptr : s.ptr = 1) (_hpc : s.tape 1 = 0) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.jzdec1 ifZero ifNonZero), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = (if ms.c1 = 0 then ifZero else ifNonZero) ∧
        s'.tape 2 = (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) ∧
        s'.tape 3 = ms.c2 ∧ s'.tape 0 = 1 ∧
        s'.tape 4 = s.tape 4 ∧ s'.tape 5 = s.tape 5 ∧ s'.tape 6 = s.tape 6 ∧
        s'.tape 8 = s.tape 8 ∧ s'.tape 9 = s.tape 9 ∧ s'.tape 10 = s.tape 10 ∧
        s'.tape 12 = s.tape 12 := by
  let a1 : State := { s with ptr := 2 }
  have h1 : RunsTo (Compiler.movePtr 1 2, s) a1 := by
    simpa only [a1] using runsTo_movePtr 1 2 s hptr
  have ha1ptr : a1.ptr = 2 := by simp only [a1]
  have ha1tape2 : a1.tape 2 = ms.c1 := by simp only [a1, hc1]
  have ha1tape3 : a1.tape 3 = ms.c2 := by simp only [a1, hc2]
  have ha1run : a1.tape 0 = 1 := by simp only [a1, hrun]
  let thenBody : Program := Compiler.movePtr 2 1 ++ Compiler.setHere ifZero ++ Compiler.movePtr 1 2
  let elseBody : Program :=
    [.dec_val] ++ Compiler.movePtr 2 1 ++ Compiler.setHere ifNonZero ++ Compiler.movePtr 1 2
  by_cases hzero : ms.c1 = 0
  · have ht0 : a1.tape 2 = 0 := by
      rw [ha1tape2]
      exact hzero
    let s_then : State :=
      { thenBodyState 2 13 14 15 16 a1 with
        tape := fun i =>
          if i = (1 : Int) then ifZero else (thenBodyState 2 13 14 15 16 a1).tape i }
    have hthen : RunsTo (thenBody, thenBodyState 2 13 14 15 16 a1) s_then := by
      have hr : RunsTo (Compiler.movePtr 2 1 ++ Compiler.setHere ifZero ++ Compiler.movePtr 1 2,
          thenBodyState 2 13 14 15 16 a1)
          { thenBodyState 2 13 14 15 16 a1 with
            tape := fun i =>
              if i = (1 : Int) then ifZero else (thenBodyState 2 13 14 15 16 a1).tape i } :=
        runsTo_jzdecThen (2 : Int) ifZero (thenBodyState 2 13 14 15 16 a1)
          (by simp only [thenBodyState])
      simpa only [thenBody, s_then] using hr
    have h1t : s_then.ptr = 2 := by simp only [s_then, thenBodyState]
    have h2t : s_then.tape 13 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (13 : Int) = 1)]
      rw [if_neg (by decide : ¬ (13 : Int) = 2)]
      rw [if_true]
    have h3t : s_then.tape 14 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (14 : Int) = 1)]
      rw [if_neg (by decide : ¬ (14 : Int) = 2)]
      rw [if_neg (by decide : ¬ (14 : Int) = 13)]
      rw [if_true]
    have h4t : s_then.tape 16 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (16 : Int) = 1)]
      rw [if_neg (by decide : ¬ (16 : Int) = 2)]
      rw [if_neg (by decide : ¬ (16 : Int) = 13)]
      rw [if_neg (by decide : ¬ (16 : Int) = 14)]
      rw [if_neg (by decide : ¬ (16 : Int) = 15)]
      rw [if_true]
    have hif : RunsTo (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody, a1)
        (ifZeroElsePost 2 13 14 15 16 s_then) :=
      runsTo_ifZeroElse_zero 2 13 14 15 16 thenBody elseBody a1 s_then ha1ptr ht0
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ hthen h1t h2t h3t h4t
    let a2 : State := ifZeroElsePost 2 13 14 15 16 s_then
    have ha2ptr : a2.ptr = 2 := by
      simp only [a2, ifZeroElsePost]
    have ha2tape1 : a2.tape 1 = ifZero := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (1 : Int) = 13), if_neg (by decide : ¬ (1 : Int) = 14),
        if_neg (by decide : ¬ (1 : Int) = 15), if_neg (by decide : ¬ (1 : Int) = 16), if_true]
    have ha2tape2 : a2.tape 2 = ms.c1 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (2 : Int) = 13)]
      rw [if_neg (by decide : ¬ (2 : Int) = 14)]
      rw [if_neg (by decide : ¬ (2 : Int) = 15)]
      rw [if_neg (by decide : ¬ (2 : Int) = 16)]
      rw [if_neg (by decide : ¬ (2 : Int) = 1)]
      simp only [thenBodyState]
      exact hzero.symm
    have ha2tape3 : a2.tape 3 = ms.c2 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (3 : Int) = 13)]
      rw [if_neg (by decide : ¬ (3 : Int) = 14)]
      rw [if_neg (by decide : ¬ (3 : Int) = 15)]
      rw [if_neg (by decide : ¬ (3 : Int) = 16)]
      rw [if_neg (by decide : ¬ (3 : Int) = 1)]
      simp only [thenBodyState]
      exact ha1tape3
    have ha2run : a2.tape 0 = 1 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (0 : Int) = 13)]
      rw [if_neg (by decide : ¬ (0 : Int) = 14)]
      rw [if_neg (by decide : ¬ (0 : Int) = 15)]
      rw [if_neg (by decide : ¬ (0 : Int) = 16)]
      rw [if_neg (by decide : ¬ (0 : Int) = 1)]
      simp only [thenBodyState]
      exact ha1run
    let a3 : State := { a2 with ptr := 1 }
    have h3 : RunsTo (Compiler.movePtr 2 1, a2) a3 := by
      simpa only [a3] using runsTo_movePtr 2 1 a2 ha2ptr
    have hchain : RunsTo (Compiler.compileInstr (.jzdec1 ifZero ifNonZero), s) a3 := by
      simpa only [Compiler.compileInstr, thenBody, elseBody, List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 2 1) a2 a3
          (RunsTo_append (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody) a1 a2 h1 hif) h3)
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_true]
    · simp only [a3, ha2tape2, hzero, if_true]
    · simp only [a3, ha2tape3]
    · simp only [a3, ha2run]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (4 : Int) = 1),
        if_neg (by decide : ¬ (4 : Int) = 2),
        if_neg (by decide : ¬ (4 : Int) = 13),
        if_neg (by decide : ¬ (4 : Int) = 14),
        if_neg (by decide : ¬ (4 : Int) = 15),
        if_neg (by decide : ¬ (4 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (5 : Int) = 1),
        if_neg (by decide : ¬ (5 : Int) = 2),
        if_neg (by decide : ¬ (5 : Int) = 13),
        if_neg (by decide : ¬ (5 : Int) = 14),
        if_neg (by decide : ¬ (5 : Int) = 15),
        if_neg (by decide : ¬ (5 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (6 : Int) = 1),
        if_neg (by decide : ¬ (6 : Int) = 2),
        if_neg (by decide : ¬ (6 : Int) = 13),
        if_neg (by decide : ¬ (6 : Int) = 14),
        if_neg (by decide : ¬ (6 : Int) = 15),
        if_neg (by decide : ¬ (6 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (8 : Int) = 1),
        if_neg (by decide : ¬ (8 : Int) = 2),
        if_neg (by decide : ¬ (8 : Int) = 13),
        if_neg (by decide : ¬ (8 : Int) = 14),
        if_neg (by decide : ¬ (8 : Int) = 15),
        if_neg (by decide : ¬ (8 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (9 : Int) = 1),
        if_neg (by decide : ¬ (9 : Int) = 2),
        if_neg (by decide : ¬ (9 : Int) = 13),
        if_neg (by decide : ¬ (9 : Int) = 14),
        if_neg (by decide : ¬ (9 : Int) = 15),
        if_neg (by decide : ¬ (9 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (10 : Int) = 1),
        if_neg (by decide : ¬ (10 : Int) = 2),
        if_neg (by decide : ¬ (10 : Int) = 13),
        if_neg (by decide : ¬ (10 : Int) = 14),
        if_neg (by decide : ¬ (10 : Int) = 15),
        if_neg (by decide : ¬ (10 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (12 : Int) = 1),
        if_neg (by decide : ¬ (12 : Int) = 2),
        if_neg (by decide : ¬ (12 : Int) = 13),
        if_neg (by decide : ¬ (12 : Int) = 14),
        if_neg (by decide : ¬ (12 : Int) = 15),
        if_neg (by decide : ¬ (12 : Int) = 16)]
  · have hw : ms.c1 = (ms.c1 - 1) + 1 := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero))]
    let w : Nat := ms.c1 - 1
    let s_else : State :=
      { elseBodyState 2 13 14 15 16 ms.c1 a1 with
        tape := fun i =>
          if i = (2 : Int) then (elseBodyState 2 13 14 15 16 ms.c1 a1).tape 2 - 1 else
          if i = (1 : Int) then ifNonZero else (elseBodyState 2 13 14 15 16 ms.c1 a1).tape i }
    have helse : RunsTo (elseBody, elseBodyState 2 13 14 15 16 ms.c1 a1) s_else := by
      have hr : RunsTo ([.dec_val] ++ Compiler.movePtr 2 1 ++ Compiler.setHere ifNonZero ++
          Compiler.movePtr 1 2, elseBodyState 2 13 14 15 16 ms.c1 a1)
          { elseBodyState 2 13 14 15 16 ms.c1 a1 with
            tape := fun i =>
              if i = (2 : Int) then (elseBodyState 2 13 14 15 16 ms.c1 a1).tape 2 - 1 else
              if i = (1 : Int) then ifNonZero else
                (elseBodyState 2 13 14 15 16 ms.c1 a1).tape i } :=
        runsTo_jzdecElse (2 : Int) ifNonZero (elseBodyState 2 13 14 15 16 ms.c1 a1)
          (by simp only [elseBodyState]) (by decide : ¬ (2 : Int) = 1)
      simpa only [elseBody, s_else] using hr
    have h1e : s_else.ptr = 2 := by simp only [s_else, elseBodyState]
    have h2e : s_else.tape 13 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (13 : Int) = 2)]
      rw [if_neg (by decide : ¬ (13 : Int) = 1)]
      rw [if_neg (by decide : ¬ (13 : Int) = 2)]
      rw [if_true]
    have h3e : s_else.tape 15 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (15 : Int) = 2)]
      rw [if_neg (by decide : ¬ (15 : Int) = 1)]
      rw [if_neg (by decide : ¬ (15 : Int) = 13)]
      rw [if_neg (by decide : ¬ (15 : Int) = 14)]
      rw [if_neg (by decide : ¬ (15 : Int) = 2)]
      rw [if_true]
    have h4e : s_else.tape 16 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (16 : Int) = 2)]
      rw [if_neg (by decide : ¬ (16 : Int) = 1)]
      rw [if_neg (by decide : ¬ (16 : Int) = 13)]
      rw [if_neg (by decide : ¬ (16 : Int) = 14)]
      rw [if_neg (by decide : ¬ (16 : Int) = 15)]
      rw [if_neg (by decide : ¬ (16 : Int) = 2)]
      rw [if_true]
    have helse' : RunsTo (elseBody, elseBodyState 2 13 14 15 16 (w + 1) a1) s_else := by
      rw [show ms.c1 = (ms.c1 - 1) + 1 from hw] at helse
      exact helse
    have hif : RunsTo (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody, a1)
        (ifZeroElsePost 2 13 14 15 16 s_else) :=
      runsTo_ifZeroElse_succ w 2 13 14 15 16 thenBody elseBody a1 s_else ha1ptr
        (ha1tape2.trans hw)
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ helse' h1e h2e h3e h4e
    let a2 : State := ifZeroElsePost 2 13 14 15 16 s_else
    have ha2ptr : a2.ptr = 2 := by
      simp only [a2, ifZeroElsePost]
    have ha2tape1 : a2.tape 1 = ifNonZero := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (1 : Int) = 13)]
      rw [if_neg (by decide : ¬ (1 : Int) = 14)]
      rw [if_neg (by decide : ¬ (1 : Int) = 15)]
      rw [if_neg (by decide : ¬ (1 : Int) = 16)]
      rw [if_neg (by decide : ¬ (1 : Int) = 2)]
      rw [if_true]
    have ha2tape2 : a2.tape 2 = ms.c1 - 1 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (2 : Int) = 13)]
      rw [if_neg (by decide : ¬ (2 : Int) = 14)]
      rw [if_neg (by decide : ¬ (2 : Int) = 15)]
      rw [if_neg (by decide : ¬ (2 : Int) = 16)]
      rw [if_neg (by decide : ¬ (2 : Int) = 1)]
      rw [if_true]
      simp only [elseBodyState, if_true]
    have ha2tape3 : a2.tape 3 = ms.c2 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (3 : Int) = 13)]
      rw [if_neg (by decide : ¬ (3 : Int) = 14)]
      rw [if_neg (by decide : ¬ (3 : Int) = 15)]
      rw [if_neg (by decide : ¬ (3 : Int) = 16)]
      rw [if_neg (by decide : ¬ (3 : Int) = 1)]
      rw [if_neg (by decide : ¬ (3 : Int) = 2)]
      simp only [elseBodyState]
      exact ha1tape3
    have ha2run : a2.tape 0 = 1 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (0 : Int) = 13)]
      rw [if_neg (by decide : ¬ (0 : Int) = 14)]
      rw [if_neg (by decide : ¬ (0 : Int) = 15)]
      rw [if_neg (by decide : ¬ (0 : Int) = 16)]
      rw [if_neg (by decide : ¬ (0 : Int) = 1)]
      rw [if_neg (by decide : ¬ (0 : Int) = 2)]
      simp only [elseBodyState]
      exact ha1run
    let a3 : State := { a2 with ptr := 1 }
    have h3 : RunsTo (Compiler.movePtr 2 1, a2) a3 := by
      simpa only [a3] using runsTo_movePtr 2 1 a2 ha2ptr
    have hchain : RunsTo (Compiler.compileInstr (.jzdec1 ifZero ifNonZero), s) a3 := by
      simpa only [Compiler.compileInstr, thenBody, elseBody, List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 2 1) a2 a3
          (RunsTo_append (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody) a1 a2 h1 hif) h3)
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_false]
    · simp only [a3, ha2tape2, hzero, if_false]
    · simp only [a3, ha2tape3]
    · simp only [a3, ha2run]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (4 : Int) = 1),
        if_neg (by decide : ¬ (4 : Int) = 2),
        if_neg (by decide : ¬ (4 : Int) = 13),
        if_neg (by decide : ¬ (4 : Int) = 14),
        if_neg (by decide : ¬ (4 : Int) = 15),
        if_neg (by decide : ¬ (4 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (5 : Int) = 1),
        if_neg (by decide : ¬ (5 : Int) = 2),
        if_neg (by decide : ¬ (5 : Int) = 13),
        if_neg (by decide : ¬ (5 : Int) = 14),
        if_neg (by decide : ¬ (5 : Int) = 15),
        if_neg (by decide : ¬ (5 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (6 : Int) = 1),
        if_neg (by decide : ¬ (6 : Int) = 2),
        if_neg (by decide : ¬ (6 : Int) = 13),
        if_neg (by decide : ¬ (6 : Int) = 14),
        if_neg (by decide : ¬ (6 : Int) = 15),
        if_neg (by decide : ¬ (6 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (8 : Int) = 1),
        if_neg (by decide : ¬ (8 : Int) = 2),
        if_neg (by decide : ¬ (8 : Int) = 13),
        if_neg (by decide : ¬ (8 : Int) = 14),
        if_neg (by decide : ¬ (8 : Int) = 15),
        if_neg (by decide : ¬ (8 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (9 : Int) = 1),
        if_neg (by decide : ¬ (9 : Int) = 2),
        if_neg (by decide : ¬ (9 : Int) = 13),
        if_neg (by decide : ¬ (9 : Int) = 14),
        if_neg (by decide : ¬ (9 : Int) = 15),
        if_neg (by decide : ¬ (9 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (10 : Int) = 1),
        if_neg (by decide : ¬ (10 : Int) = 2),
        if_neg (by decide : ¬ (10 : Int) = 13),
        if_neg (by decide : ¬ (10 : Int) = 14),
        if_neg (by decide : ¬ (10 : Int) = 15),
        if_neg (by decide : ¬ (10 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (12 : Int) = 1),
        if_neg (by decide : ¬ (12 : Int) = 2),
        if_neg (by decide : ¬ (12 : Int) = 13),
        if_neg (by decide : ¬ (12 : Int) = 14),
        if_neg (by decide : ¬ (12 : Int) = 15),
        if_neg (by decide : ¬ (12 : Int) = 16)]


theorem runsTo_compileInstr_jzdec2 (ifZero ifNonZero : Nat) (ms : Minsky.State)
    (s : State)
    (hptr : s.ptr = 1) (_hpc : s.tape 1 = 0) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.jzdec2 ifZero ifNonZero), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = (if ms.c2 = 0 then ifZero else ifNonZero) ∧
        s'.tape 2 = ms.c1 ∧
        s'.tape 3 = (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) ∧ s'.tape 0 = 1 ∧
        s'.tape 4 = s.tape 4 ∧ s'.tape 5 = s.tape 5 ∧ s'.tape 6 = s.tape 6 ∧
        s'.tape 8 = s.tape 8 ∧ s'.tape 9 = s.tape 9 ∧ s'.tape 10 = s.tape 10 ∧
        s'.tape 12 = s.tape 12 := by
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
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_true]
    · simp only [a3, ha2tape2]
    · simp only [a3, ha2tape3, hzero, if_true]
    · simp only [a3, ha2run]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (4 : Int) = 1),
        if_neg (by decide : ¬ (4 : Int) = 3),
        if_neg (by decide : ¬ (4 : Int) = 13),
        if_neg (by decide : ¬ (4 : Int) = 14),
        if_neg (by decide : ¬ (4 : Int) = 15),
        if_neg (by decide : ¬ (4 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (5 : Int) = 1),
        if_neg (by decide : ¬ (5 : Int) = 3),
        if_neg (by decide : ¬ (5 : Int) = 13),
        if_neg (by decide : ¬ (5 : Int) = 14),
        if_neg (by decide : ¬ (5 : Int) = 15),
        if_neg (by decide : ¬ (5 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (6 : Int) = 1),
        if_neg (by decide : ¬ (6 : Int) = 3),
        if_neg (by decide : ¬ (6 : Int) = 13),
        if_neg (by decide : ¬ (6 : Int) = 14),
        if_neg (by decide : ¬ (6 : Int) = 15),
        if_neg (by decide : ¬ (6 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (8 : Int) = 1),
        if_neg (by decide : ¬ (8 : Int) = 3),
        if_neg (by decide : ¬ (8 : Int) = 13),
        if_neg (by decide : ¬ (8 : Int) = 14),
        if_neg (by decide : ¬ (8 : Int) = 15),
        if_neg (by decide : ¬ (8 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (9 : Int) = 1),
        if_neg (by decide : ¬ (9 : Int) = 3),
        if_neg (by decide : ¬ (9 : Int) = 13),
        if_neg (by decide : ¬ (9 : Int) = 14),
        if_neg (by decide : ¬ (9 : Int) = 15),
        if_neg (by decide : ¬ (9 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (10 : Int) = 1),
        if_neg (by decide : ¬ (10 : Int) = 3),
        if_neg (by decide : ¬ (10 : Int) = 13),
        if_neg (by decide : ¬ (10 : Int) = 14),
        if_neg (by decide : ¬ (10 : Int) = 15),
        if_neg (by decide : ¬ (10 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (12 : Int) = 1),
        if_neg (by decide : ¬ (12 : Int) = 3),
        if_neg (by decide : ¬ (12 : Int) = 13),
        if_neg (by decide : ¬ (12 : Int) = 14),
        if_neg (by decide : ¬ (12 : Int) = 15),
        if_neg (by decide : ¬ (12 : Int) = 16)]
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
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_false]
    · simp only [a3, ha2tape2]
    · simp only [a3, ha2tape3, hzero, if_false]
    · simp only [a3, ha2run]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (4 : Int) = 1),
        if_neg (by decide : ¬ (4 : Int) = 3),
        if_neg (by decide : ¬ (4 : Int) = 13),
        if_neg (by decide : ¬ (4 : Int) = 14),
        if_neg (by decide : ¬ (4 : Int) = 15),
        if_neg (by decide : ¬ (4 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (5 : Int) = 1),
        if_neg (by decide : ¬ (5 : Int) = 3),
        if_neg (by decide : ¬ (5 : Int) = 13),
        if_neg (by decide : ¬ (5 : Int) = 14),
        if_neg (by decide : ¬ (5 : Int) = 15),
        if_neg (by decide : ¬ (5 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (6 : Int) = 1),
        if_neg (by decide : ¬ (6 : Int) = 3),
        if_neg (by decide : ¬ (6 : Int) = 13),
        if_neg (by decide : ¬ (6 : Int) = 14),
        if_neg (by decide : ¬ (6 : Int) = 15),
        if_neg (by decide : ¬ (6 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (8 : Int) = 1),
        if_neg (by decide : ¬ (8 : Int) = 3),
        if_neg (by decide : ¬ (8 : Int) = 13),
        if_neg (by decide : ¬ (8 : Int) = 14),
        if_neg (by decide : ¬ (8 : Int) = 15),
        if_neg (by decide : ¬ (8 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (9 : Int) = 1),
        if_neg (by decide : ¬ (9 : Int) = 3),
        if_neg (by decide : ¬ (9 : Int) = 13),
        if_neg (by decide : ¬ (9 : Int) = 14),
        if_neg (by decide : ¬ (9 : Int) = 15),
        if_neg (by decide : ¬ (9 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (10 : Int) = 1),
        if_neg (by decide : ¬ (10 : Int) = 3),
        if_neg (by decide : ¬ (10 : Int) = 13),
        if_neg (by decide : ¬ (10 : Int) = 14),
        if_neg (by decide : ¬ (10 : Int) = 15),
        if_neg (by decide : ¬ (10 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (12 : Int) = 1),
        if_neg (by decide : ¬ (12 : Int) = 3),
        if_neg (by decide : ¬ (12 : Int) = 13),
        if_neg (by decide : ¬ (12 : Int) = 14),
        if_neg (by decide : ¬ (12 : Int) = 15),
        if_neg (by decide : ¬ (12 : Int) = 16)]


/-- The state in which `block` runs inside a window: the `done` flag is set and
    the pointer is back on the `pc` cell. -/
def windowBlockStart (s : State) : State :=
  let hd0 : State := { thenBodyState 4 5 6 7 8 s with ptr := 1 }
  let sT : State := thenBodyState 1 9 10 11 12 hd0
  let m1 : State := { sT with ptr := 4 }
  let m2 : State := { m1 with tape := fun i => if i = (4 : Int) then m1.tape 4 + 1 else m1.tape i }
  { m2 with ptr := 1 }

/-- A window whose `pc` cell is zero runs `block` exactly once and sets the
    `done` flag. -/
theorem runsTo_window_match (block : Program) (ms ms' : Minsky.State) (s s'' : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) (hpc : ms.pc = 0)
    (hblock : RunsTo (block, windowBlockStart s) s'')
    (hpost : s''.ptr = 1 ∧ s''.tape 1 = ms'.pc ∧ s''.tape 2 = ms'.c1 ∧
      s''.tape 3 = ms'.c2 ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
      s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
      s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0) :
    ∃ s', RunsTo (Compiler.window block, s) s' ∧
      s'.ptr = 4 ∧ s'.tape 1 = ms'.pc ∧ s'.tape 2 = ms'.c1 ∧
        s'.tape 3 = ms'.c2 ∧ s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧
        s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧ s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  rcases hsim with ⟨hsptr, hspc, hsc1, hsc2, hsrunning⟩
  rcases hpost with ⟨hpptr, hppc, hpc1, hpc2, hprun, hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
  let innerThen : Program := Compiler.movePtr 1 4 ++ [.inc_val] ++ Compiler.movePtr 4 1 ++ block
  let tb : Program := Compiler.movePtr 4 1 ++
    Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++ Compiler.movePtr 1 4
  have hsptr4 : s.ptr = 4 := hsptr
  have hspc0 : s.tape 1 = 0 := by
    rw [hspc]
    exact hpc
  let hd0 : State := { thenBodyState 4 5 6 7 8 s with ptr := 1 }
  have hd0ptr : hd0.ptr = 1 := by simp only [hd0]
  have hd0pc : hd0.tape 1 = 0 := by
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (1 : Int) = 4), if_neg (by decide : ¬ (1 : Int) = 5),
      if_neg (by decide : ¬ (1 : Int) = 6), if_neg (by decide : ¬ (1 : Int) = 7),
      if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hspc0
  let sT : State := thenBodyState 1 9 10 11 12 hd0
  have hs1 : sT.ptr = 1 := by simp only [sT, thenBodyState]
  -- the inner then body: move to done, set it, move back, run block
  let m1 : State := { sT with ptr := 4 }
  let m2 : State := { m1 with tape := fun i => if i = (4 : Int) then 1 else m1.tape i }
  have hd0tape4 : hd0.tape 4 = 0 := by
    simp only [hd0, thenBodyState]
    rw [if_true]
  have hs4 : sT.tape 4 = 0 := by
    simp only [sT, thenBodyState]
    rw [if_neg (by decide : ¬ (4 : Int) = 1), if_neg (by decide : ¬ (4 : Int) = 9),
      if_neg (by decide : ¬ (4 : Int) = 10), if_neg (by decide : ¬ (4 : Int) = 11),
      if_neg (by decide : ¬ (4 : Int) = 12)]
    exact hd0tape4
  have hm1 : RunsTo (Compiler.movePtr 1 4, sT) m1 := by
    simpa only [m1] using runsTo_movePtr 1 4 sT hs1
  have hm2 : RunsTo ([.inc_val], m1) m2 := by
    have hinc : RunsTo ([.inc_val], m1)
        { m1 with tape := fun i => if i = m1.ptr then m1.tape m1.ptr + 1 else m1.tape i } :=
      runsTo_inc_val m1
    have heq : { m1 with tape := fun i => if i = m1.ptr then m1.tape m1.ptr + 1 else m1.tape i }
        = m2 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (4 : Int)
        · simp only [hi, if_true, m2, m1, hs4]
        · simp only [if_neg hi, m2, m1]
      · rfl
      · rfl
    rw [heq] at hinc
    exact hinc
  have hm2ptr : m2.ptr = 4 := by simp only [m2, m1]
  have hm3 : RunsTo (Compiler.movePtr 4 1, m2) (windowBlockStart s) := by
    simpa only using runsTo_movePtr 4 1 m2 hm2ptr
  have hinner : RunsTo (innerThen, sT) s'' := by
    have hc : RunsTo (Compiler.movePtr 1 4 ++ [.inc_val] ++ Compiler.movePtr 4 1 ++ block,
        sT) s'' :=
      RunsTo_append block (windowBlockStart s) s''
        (RunsTo_append (Compiler.movePtr 4 1) m2 (windowBlockStart s)
          (RunsTo_append [.inc_val] m1 m2 hm1 hm2) hm3)
        hblock
    simpa only [innerThen, List.append_assoc] using hc
  have hifInner : RunsTo (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val], hd0)
      (ifZeroElsePost 1 9 10 11 12 s'') :=
    runsTo_ifZeroElse_zero 1 9 10 11 12 innerThen [.dec_val] hd0 s'' hd0ptr hd0pc
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ hinner hpptr hp9 hp10 hp12
  let iPost : State := ifZeroElsePost 1 9 10 11 12 s''
  have hiPtr : iPost.ptr = 1 := by
    simp only [iPost, ifZeroElsePost]
  have hiPc : iPost.tape 1 = ms'.pc := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (1 : Int) = 9), if_neg (by decide : ¬ (1 : Int) = 10),
      if_neg (by decide : ¬ (1 : Int) = 11), if_neg (by decide : ¬ (1 : Int) = 12)]
    exact hppc
  have hiC1 : iPost.tape 2 = ms'.c1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (2 : Int) = 9), if_neg (by decide : ¬ (2 : Int) = 10),
      if_neg (by decide : ¬ (2 : Int) = 11), if_neg (by decide : ¬ (2 : Int) = 12)]
    exact hpc1
  have hiC2 : iPost.tape 3 = ms'.c2 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (3 : Int) = 9), if_neg (by decide : ¬ (3 : Int) = 10),
      if_neg (by decide : ¬ (3 : Int) = 11), if_neg (by decide : ¬ (3 : Int) = 12)]
    exact hpc2
  have hiRun : iPost.tape 0 = 1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (0 : Int) = 9), if_neg (by decide : ¬ (0 : Int) = 10),
      if_neg (by decide : ¬ (0 : Int) = 11), if_neg (by decide : ¬ (0 : Int) = 12)]
    exact hprun
  have hiDone : iPost.tape 4 = 1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (4 : Int) = 9), if_neg (by decide : ¬ (4 : Int) = 10),
      if_neg (by decide : ¬ (4 : Int) = 11), if_neg (by decide : ¬ (4 : Int) = 12)]
    exact hp4
  let s_then : State := { iPost with ptr := 4 }
  have h1 : RunsTo (Compiler.movePtr 1 4, iPost) s_then := by
    simpa only [s_then] using runsTo_movePtr 1 4 iPost hiPtr
  have hThen : RunsTo (tb, thenBodyState 4 5 6 7 8 s) s_then := by
    have hc : RunsTo (Compiler.movePtr 4 1 ++
        Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++ Compiler.movePtr 1 4,
        thenBodyState 4 5 6 7 8 s) s_then :=
      RunsTo_append (Compiler.movePtr 1 4) iPost s_then
        (RunsTo_append (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val]) hd0 iPost
          (runsTo_movePtr 4 1 (thenBodyState 4 5 6 7 8 s) (by simp only [thenBodyState]))
          hifInner)
        h1
    simpa only [tb, List.append_assoc] using hc
  have h1t : s_then.ptr = 4 := by simp only [s_then]
  have h2t : s_then.tape 5 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (5 : Int) = 9), if_neg (by decide : ¬ (5 : Int) = 10),
      if_neg (by decide : ¬ (5 : Int) = 11), if_neg (by decide : ¬ (5 : Int) = 12)]
    exact hp5
  have h3t : s_then.tape 6 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 9), if_neg (by decide : ¬ (6 : Int) = 10),
      if_neg (by decide : ¬ (6 : Int) = 11), if_neg (by decide : ¬ (6 : Int) = 12)]
    exact hp6
  have h4t : s_then.tape 8 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 9), if_neg (by decide : ¬ (8 : Int) = 10),
      if_neg (by decide : ¬ (8 : Int) = 11), if_neg (by decide : ¬ (8 : Int) = 12)]
    exact hp8
  have hOuter : RunsTo (Compiler.ifZeroElse 4 5 6 7 8 tb [], s)
      (ifZeroElsePost 4 5 6 7 8 s_then) :=
    runsTo_ifZeroElse_zero 4 5 6 7 8 tb [] s s_then hsptr4 hdone
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ hThen h1t h2t h3t h4t
  have hprog : Compiler.window block = Compiler.ifZeroElse 4 5 6 7 8 tb [] := by
    simp only [Compiler.window, tb, innerThen, List.append_assoc]
  let a2 : State := ifZeroElsePost 4 5 6 7 8 s_then
  have ha2ptr : a2.ptr = 4 := by
    simp only [a2, ifZeroElsePost]
  have ha2tape1 : a2.tape 1 = ms'.pc := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (1 : Int) = 5), if_neg (by decide : ¬ (1 : Int) = 6),
      if_neg (by decide : ¬ (1 : Int) = 7), if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hiPc
  have ha2tape2 : a2.tape 2 = ms'.c1 := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (2 : Int) = 5), if_neg (by decide : ¬ (2 : Int) = 6),
      if_neg (by decide : ¬ (2 : Int) = 7), if_neg (by decide : ¬ (2 : Int) = 8)]
    exact hiC1
  have ha2tape3 : a2.tape 3 = ms'.c2 := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (3 : Int) = 5), if_neg (by decide : ¬ (3 : Int) = 6),
      if_neg (by decide : ¬ (3 : Int) = 7), if_neg (by decide : ¬ (3 : Int) = 8)]
    exact hiC2
  have ha2tape4 : a2.tape 4 = 1 := by
    simp only [a2, ifZeroElsePost]
    exact hiDone
  have ha2run : a2.tape 0 = 1 := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (0 : Int) = 5), if_neg (by decide : ¬ (0 : Int) = 6),
      if_neg (by decide : ¬ (0 : Int) = 7), if_neg (by decide : ¬ (0 : Int) = 8)]
    exact hiRun
  have ha2tape5 : a2.tape 5 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_true]
  have ha2tape6 : a2.tape 6 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 5), if_true]
  have ha2tape7 : a2.tape 7 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (7 : Int) = 5), if_neg (by decide : ¬ (7 : Int) = 6), if_true]
  have ha2tape8 : a2.tape 8 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 5), if_neg (by decide : ¬ (8 : Int) = 6),
      if_neg (by decide : ¬ (8 : Int) = 7), if_true]
  have hwin : RunsTo (Compiler.window block, s) a2 := by
    simpa only [hprog] using hOuter
  exact ⟨a2, hwin, ha2ptr, ha2tape1, ha2tape2, ha2tape3, ha2tape4, ha2run, ha2tape5,
    ha2tape6, ha2tape7, ha2tape8⟩



/-- A single `-` decrements the current cell. -/
theorem runsTo_dec_val (s : State) :
    RunsTo ([.dec_val], s)
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

/-- A window whose `pc` cell is non-zero decrements it and does nothing else. -/
theorem runsTo_window_skip (block : Program) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) (hpc : ms.pc ≠ 0) :
    ∃ s', RunsTo (Compiler.window block, s) s' ∧
      s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧
        s'.tape 3 = ms.c2 ∧ s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧
        s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧ s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  rcases hsim with ⟨hsptr, hspc, hsc1, hsc2, hsrunning⟩
  let hd0 : State := { thenBodyState 4 5 6 7 8 s with ptr := 1 }
  have hd0ptr : hd0.ptr = 1 := by simp only [hd0]
  have hd0pc : hd0.tape 1 = ms.pc := by
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (1 : Int) = 4)]
    rw [if_neg (by decide : ¬ (1 : Int) = 5)]
    rw [if_neg (by decide : ¬ (1 : Int) = 6)]
    rw [if_neg (by decide : ¬ (1 : Int) = 7)]
    rw [if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hspc
  have hw : ms.pc = (ms.pc - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpc))]
  let w : Nat := ms.pc - 1
  let s_else : State :=
    { elseBodyState 1 9 10 11 12 ms.pc hd0 with
      tape := fun i =>
        if i = (1 : Int) then (elseBodyState 1 9 10 11 12 ms.pc hd0).tape 1 - 1 else
        (elseBodyState 1 9 10 11 12 ms.pc hd0).tape i }
  have helse : RunsTo ([.dec_val], elseBodyState 1 9 10 11 12 ms.pc hd0) s_else := by
    have hdec : RunsTo ([.dec_val], elseBodyState 1 9 10 11 12 ms.pc hd0)
        { elseBodyState 1 9 10 11 12 ms.pc hd0 with tape := fun i =>
          if i = (1 : Int) then (elseBodyState 1 9 10 11 12 ms.pc hd0).tape 1 - 1 else
          (elseBodyState 1 9 10 11 12 ms.pc hd0).tape i } :=
      runsTo_dec_val (elseBodyState 1 9 10 11 12 ms.pc hd0)
    simpa only [s_else] using hdec
  have h1e : s_else.ptr = 1 := by simp only [s_else, elseBodyState]
  have h2e : s_else.tape 9 = 0 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (9 : Int) = 1)]
    rw [if_neg (by decide : ¬ (9 : Int) = 1)]
    rw [if_true]
  have h3e : s_else.tape 11 = 0 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (11 : Int) = 1)]
    rw [if_neg (by decide : ¬ (11 : Int) = 1)]
    rw [if_neg (by decide : ¬ (11 : Int) = 9)]
    rw [if_neg (by decide : ¬ (11 : Int) = 10)]
    rw [if_true]
  have h4e : s_else.tape 12 = 0 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (12 : Int) = 1)]
    rw [if_neg (by decide : ¬ (12 : Int) = 1)]
    rw [if_neg (by decide : ¬ (12 : Int) = 9)]
    rw [if_neg (by decide : ¬ (12 : Int) = 10)]
    rw [if_neg (by decide : ¬ (12 : Int) = 11)]
    rw [if_true]
  have hs1 : s_else.tape 1 = ms.pc - 1 := by
    simp only [s_else, elseBodyState]
    rw [if_true]
    rw [if_true]
  have hs2 : s_else.tape 2 = ms.c1 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (2 : Int) = 1)]
    rw [if_neg (by decide : ¬ (2 : Int) = 9)]
    rw [if_neg (by decide : ¬ (2 : Int) = 10)]
    rw [if_neg (by decide : ¬ (2 : Int) = 11)]
    rw [if_neg (by decide : ¬ (2 : Int) = 12)]
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (2 : Int) = 4)]
    rw [if_neg (by decide : ¬ (2 : Int) = 5)]
    rw [if_neg (by decide : ¬ (2 : Int) = 6)]
    rw [if_neg (by decide : ¬ (2 : Int) = 7)]
    rw [if_neg (by decide : ¬ (2 : Int) = 8)]
    exact hsc1
  have hs3 : s_else.tape 3 = ms.c2 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (3 : Int) = 1)]
    rw [if_neg (by decide : ¬ (3 : Int) = 9)]
    rw [if_neg (by decide : ¬ (3 : Int) = 10)]
    rw [if_neg (by decide : ¬ (3 : Int) = 11)]
    rw [if_neg (by decide : ¬ (3 : Int) = 12)]
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (3 : Int) = 4)]
    rw [if_neg (by decide : ¬ (3 : Int) = 5)]
    rw [if_neg (by decide : ¬ (3 : Int) = 6)]
    rw [if_neg (by decide : ¬ (3 : Int) = 7)]
    rw [if_neg (by decide : ¬ (3 : Int) = 8)]
    exact hsc2
  have hs4 : s_else.tape 4 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (4 : Int) = 1),
      if_neg (by decide : ¬ (4 : Int) = 9),
      if_neg (by decide : ¬ (4 : Int) = 10),
      if_neg (by decide : ¬ (4 : Int) = 11),
      if_neg (by decide : ¬ (4 : Int) = 12),
      if_true]
  have hs0 : s_else.tape 0 = 1 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (0 : Int) = 1)]
    rw [if_neg (by decide : ¬ (0 : Int) = 9)]
    rw [if_neg (by decide : ¬ (0 : Int) = 10)]
    rw [if_neg (by decide : ¬ (0 : Int) = 11)]
    rw [if_neg (by decide : ¬ (0 : Int) = 12)]
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (0 : Int) = 4)]
    rw [if_neg (by decide : ¬ (0 : Int) = 5)]
    rw [if_neg (by decide : ¬ (0 : Int) = 6)]
    rw [if_neg (by decide : ¬ (0 : Int) = 7)]
    rw [if_neg (by decide : ¬ (0 : Int) = 8)]
    exact hsrunning
  have hs5 : s_else.tape 5 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (5 : Int) = 1),
      if_neg (by decide : ¬ (5 : Int) = 9),
      if_neg (by decide : ¬ (5 : Int) = 10),
      if_neg (by decide : ¬ (5 : Int) = 11),
      if_neg (by decide : ¬ (5 : Int) = 12),
      if_neg (by decide : ¬ (5 : Int) = 4),
      if_true]
  have hs6 : s_else.tape 6 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (6 : Int) = 1),
      if_neg (by decide : ¬ (6 : Int) = 9),
      if_neg (by decide : ¬ (6 : Int) = 10),
      if_neg (by decide : ¬ (6 : Int) = 11),
      if_neg (by decide : ¬ (6 : Int) = 12),
      if_neg (by decide : ¬ (6 : Int) = 4),
      if_neg (by decide : ¬ (6 : Int) = 5),
      if_true]
  have hs8 : s_else.tape 8 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (8 : Int) = 1),
      if_neg (by decide : ¬ (8 : Int) = 9),
      if_neg (by decide : ¬ (8 : Int) = 10),
      if_neg (by decide : ¬ (8 : Int) = 11),
      if_neg (by decide : ¬ (8 : Int) = 12),
      if_neg (by decide : ¬ (8 : Int) = 4),
      if_neg (by decide : ¬ (8 : Int) = 5),
      if_neg (by decide : ¬ (8 : Int) = 6),
      if_neg (by decide : ¬ (8 : Int) = 7),
      if_true]
  have helse' : RunsTo ([.dec_val], elseBodyState 1 9 10 11 12 (w + 1) hd0) s_else := by
    rw [show ms.pc = (ms.pc - 1) + 1 from hw] at helse
    exact helse
  let innerThen : Program := Compiler.movePtr 1 4 ++ [.inc_val] ++ Compiler.movePtr 4 1 ++ block
  have hv : hd0.tape 1 = w + 1 := by
    rw [hd0pc]
    exact hw
  have hifInner : RunsTo (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val], hd0)
      (ifZeroElsePost 1 9 10 11 12 s_else) :=
    runsTo_ifZeroElse_succ w 1 9 10 11 12 innerThen [.dec_val]
      hd0 s_else hd0ptr hv
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ helse' h1e h2e h3e h4e
  let iPost : State := ifZeroElsePost 1 9 10 11 12 s_else
  have hiPtr : iPost.ptr = 1 := by rfl
  have hiPc : iPost.tape 1 = ms.pc - 1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (1 : Int) = 9), if_neg (by decide : ¬ (1 : Int) = 10),
      if_neg (by decide : ¬ (1 : Int) = 11), if_neg (by decide : ¬ (1 : Int) = 12)]
    exact hs1
  have hiC1 : iPost.tape 2 = ms.c1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (2 : Int) = 9), if_neg (by decide : ¬ (2 : Int) = 10),
      if_neg (by decide : ¬ (2 : Int) = 11), if_neg (by decide : ¬ (2 : Int) = 12)]
    exact hs2
  have hiC2 : iPost.tape 3 = ms.c2 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (3 : Int) = 9), if_neg (by decide : ¬ (3 : Int) = 10),
      if_neg (by decide : ¬ (3 : Int) = 11), if_neg (by decide : ¬ (3 : Int) = 12)]
    exact hs3
  have hiRun : iPost.tape 0 = 1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (0 : Int) = 9), if_neg (by decide : ¬ (0 : Int) = 10),
      if_neg (by decide : ¬ (0 : Int) = 11), if_neg (by decide : ¬ (0 : Int) = 12)]
    exact hs0
  have hiDone : iPost.tape 4 = 0 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (4 : Int) = 9), if_neg (by decide : ¬ (4 : Int) = 10),
      if_neg (by decide : ¬ (4 : Int) = 11), if_neg (by decide : ¬ (4 : Int) = 12)]
    exact hs4
  let s_then : State := { iPost with ptr := 4 }
  have h1 : RunsTo (Compiler.movePtr 1 4, iPost) s_then := by
    simpa only [s_then] using runsTo_movePtr 1 4 iPost hiPtr
  have hThen : RunsTo (Compiler.movePtr 4 1 ++
      Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
      Compiler.movePtr 1 4, thenBodyState 4 5 6 7 8 s) s_then :=
    RunsTo_append (Compiler.movePtr 1 4) iPost s_then
      (RunsTo_append (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val]) hd0 iPost
        (runsTo_movePtr 4 1 (thenBodyState 4 5 6 7 8 s) (by simp only [thenBodyState]))
        hifInner)
      h1
  have h1t : s_then.ptr = 4 := by simp only [s_then]
  have h2t : s_then.tape 5 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (5 : Int) = 9), if_neg (by decide : ¬ (5 : Int) = 10),
      if_neg (by decide : ¬ (5 : Int) = 11), if_neg (by decide : ¬ (5 : Int) = 12)]
    exact hs5
  have h3t : s_then.tape 6 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 9), if_neg (by decide : ¬ (6 : Int) = 10),
      if_neg (by decide : ¬ (6 : Int) = 11), if_neg (by decide : ¬ (6 : Int) = 12)]
    exact hs6
  have h4t : s_then.tape 8 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 9), if_neg (by decide : ¬ (8 : Int) = 10),
      if_neg (by decide : ¬ (8 : Int) = 11), if_neg (by decide : ¬ (8 : Int) = 12)]
    exact hs8
  have hOuter : RunsTo (Compiler.ifZeroElse 4 5 6 7 8
      (Compiler.movePtr 4 1 ++ Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
        Compiler.movePtr 1 4) [], s)
      (ifZeroElsePost 4 5 6 7 8 s_then) :=
    runsTo_ifZeroElse_zero 4 5 6 7 8
      (Compiler.movePtr 4 1 ++ Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
        Compiler.movePtr 1 4) [] s s_then hsptr hdone
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ hThen h1t h2t h3t h4t
  have hprog : Compiler.window block = Compiler.ifZeroElse 4 5 6 7 8
      (Compiler.movePtr 4 1 ++ Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
        Compiler.movePtr 1 4) [] := by
    simp only [Compiler.window, innerThen, List.append_assoc]
  let a2 : State := ifZeroElsePost 4 5 6 7 8 s_then
  have ha2ptr : a2.ptr = 4 := by simp only [a2, ifZeroElsePost]
  have ha2tape1 : a2.tape 1 = ms.pc - 1 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (1 : Int) = 5), if_neg (by decide : ¬ (1 : Int) = 6),
      if_neg (by decide : ¬ (1 : Int) = 7), if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hiPc
  have ha2tape2 : a2.tape 2 = ms.c1 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (2 : Int) = 5), if_neg (by decide : ¬ (2 : Int) = 6),
      if_neg (by decide : ¬ (2 : Int) = 7), if_neg (by decide : ¬ (2 : Int) = 8)]
    exact hiC1
  have ha2tape3 : a2.tape 3 = ms.c2 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (3 : Int) = 5), if_neg (by decide : ¬ (3 : Int) = 6),
      if_neg (by decide : ¬ (3 : Int) = 7), if_neg (by decide : ¬ (3 : Int) = 8)]
    exact hiC2
  have ha2tape4 : a2.tape 4 = 0 := by
    simp only [a2, ifZeroElsePost]
    exact hiDone
  have ha2run : a2.tape 0 = 1 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (0 : Int) = 5), if_neg (by decide : ¬ (0 : Int) = 6),
      if_neg (by decide : ¬ (0 : Int) = 7), if_neg (by decide : ¬ (0 : Int) = 8)]
    exact hiRun
  have ha2tape5 : a2.tape 5 = 0 := by simp only [a2, ifZeroElsePost]; rw [if_true]
  have ha2tape6 : a2.tape 6 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 5), if_true]
  have ha2tape7 : a2.tape 7 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (7 : Int) = 5), if_neg (by decide : ¬ (7 : Int) = 6), if_true]
  have ha2tape8 : a2.tape 8 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 5), if_neg (by decide : ¬ (8 : Int) = 6),
      if_neg (by decide : ¬ (8 : Int) = 7), if_true]
  have hwin : RunsTo (Compiler.window block, s) a2 := by
    simpa only [hprog] using hOuter
  exact ⟨a2, hwin, ha2ptr, ha2tape1, ha2tape2, ha2tape3, ha2tape4, ha2run, ha2tape5,
    ha2tape6, ha2tape7, ha2tape8⟩



/-- The prepared window state keeps the running flag and counters, clears the
    `pc`, and sets the `done` flag and the two window flags. -/
theorem windowBlockStart_tape (s : State) :
    (windowBlockStart s).ptr = 1 ∧ (windowBlockStart s).tape 1 = 0 ∧
    (windowBlockStart s).tape 2 = s.tape 2 ∧ (windowBlockStart s).tape 3 = s.tape 3 ∧
    (windowBlockStart s).tape 0 = s.tape 0 ∧ (windowBlockStart s).tape 4 = 1 ∧
    (windowBlockStart s).tape 5 = 0 ∧ (windowBlockStart s).tape 6 = 0 ∧
    (windowBlockStart s).tape 8 = 0 ∧ (windowBlockStart s).tape 9 = 0 ∧
    (windowBlockStart s).tape 10 = 0 ∧ (windowBlockStart s).tape 12 = 0 := by
  repeat' constructor


/-- The `inc1` window: if the `pc` is zero, run the `inc1` block and set
    `done`; otherwise decrement the `pc`. -/
theorem runsTo_window_inc1 (next : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.inc1 next)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 + 1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_inc1 next ms b0 hb0ptr hb0pc hb0c1 hb0c2 hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = next ∧ s''.tape 2 = ms.c1 + 1 ∧
        s''.tape 3 = ms.c2 ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State := { pc := next, c1 := ms.c1 + 1, c2 := ms.c2 }
    rcases runsTo_window_match (Compiler.compileInstr (.inc1 next)) ms ms' s s''
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.inc1 next)) ms s hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩



theorem runsTo_window_inc2 (next : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.inc2 next)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 + 1 ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_inc2 next ms b0 hb0ptr hb0pc hb0c1 hb0c2 hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = next ∧ s''.tape 2 = ms.c1 ∧
        s''.tape 3 = ms.c2 + 1 ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State := { pc := next, c1 := ms.c1, c2 := ms.c2 + 1 }
    rcases runsTo_window_match (Compiler.compileInstr (.inc2 next)) ms ms' s s''
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.inc2 next)) ms s hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩



theorem runsTo_window_jzdec1 (ifZero ifNonZero : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.jzdec1 ifZero ifNonZero)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = (if ms.c1 = 0 then ifZero else ifNonZero) ∧
          s'.tape 2 = (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_jzdec1 ifZero ifNonZero ms b0 hb0ptr hb0pc hb0c1 hb0c2
        hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = (if ms.c1 = 0 then ifZero else ifNonZero) ∧
        s''.tape 2 = (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) ∧
        s''.tape 3 = ms.c2 ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State :=
      { pc := (if ms.c1 = 0 then ifZero else ifNonZero),
        c1 := (if ms.c1 = 0 then ms.c1 else ms.c1 - 1), c2 := ms.c2 }
    rcases runsTo_window_match (Compiler.compileInstr (.jzdec1 ifZero ifNonZero)) ms ms' s s''
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.jzdec1 ifZero ifNonZero)) ms s
        hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩



theorem runsTo_window_jzdec2 (ifZero ifNonZero : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.jzdec2 ifZero ifNonZero)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = (if ms.c2 = 0 then ifZero else ifNonZero) ∧
          s'.tape 2 = ms.c1 ∧ s'.tape 3 = (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_jzdec2 ifZero ifNonZero ms b0 hb0ptr hb0pc hb0c1 hb0c2 hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = (if ms.c2 = 0 then ifZero else ifNonZero) ∧
        s''.tape 2 = ms.c1 ∧
        s''.tape 3 = (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State :=
      { pc := (if ms.c2 = 0 then ifZero else ifNonZero),
        c1 := ms.c1, c2 := (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) }
    rcases runsTo_window_match (Compiler.compileInstr (.jzdec2 ifZero ifNonZero)) ms ms' s s''
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.jzdec2 ifZero ifNonZero)) ms s
        hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩



end LeanBF
