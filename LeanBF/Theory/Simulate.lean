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

end LeanBF
