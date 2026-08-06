/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics
import LeanBF.Theory.Loop
import LeanBF.Theory.State

/-!
# Semantics Lemmas

Single-step behavior of the interpreter: a theorem for every instruction
(pointer movement, cell arithmetic, input/output, and the loop), plus the
basic `run`/`halts` facts.

## Theorems

* `step_empty`: The empty program has no step.
* `step_incPtr`: A single `>` moves the pointer.
* `step_decPtr`: A single `<` moves the pointer.
* `step_incVal`: A single `+` increments the current cell.
* `step_decVal`: A single `-` decrements the current cell.
* `step_read_nil`: A `,` at end-of-input writes `0` to the current cell.
* `step_read_cons`: A `,` with available input writes it to the current cell.
* `step_write`: A `.` appends the current value to the output.
* `step_loop_zero`: A `[` with current value `0` skips its body.
* `step_loop_nonzero`: A `[` with a non-zero current value runs its body and
  re-queues the loop.
* `run_zero`: Running for zero steps returns the state.
* `run_empty`: The empty program halts immediately.
* `stepsToHalt_empty`: The empty program takes zero steps to halt.
* `halts_empty`: The empty program halts.
* `step_cons_ne_none`: A non-empty program always has a step.
* `stepsToHalt_one_eq_zero`: `stepsToHalt 1` is `0` exactly on the empty
  program.
* `loop_incVal_stepsToHalt`: A non-zero cell makes `[+ ]` run forever, taking
  n steps in any n-step window.
* `loop_incVal_never_halts`: `[+ ]` never halts from a non-zero cell.
* `read_write_echo`: Reading a value and writing it back echoes it.
* `runSeq_write_write_output`: Writing twice appends two copies of the
  current value.
* `runSeq_read_input`: Reading `k` times consumes the first `k` inputs.
-/

namespace LeanBF

/-- The empty program has no step. -/
theorem step_empty (s : State) : step [] s = none :=
  rfl

/-- A single `>` moves the pointer. -/
theorem step_incPtr (s : State) : step [.inc_ptr] s = some ([], s.incPtr) :=
  rfl

/-- A single `<` moves the pointer. -/
theorem step_decPtr (s : State) : step [.dec_ptr] s = some ([], s.decPtr) :=
  rfl

/-- A single `+` increments the current cell. -/
theorem step_incVal (s : State) : step [.inc_val] s = some ([], s.incVal) :=
  rfl

/-- A single `-` decrements the current cell. -/
theorem step_decVal (s : State) : step [.dec_val] s = some ([], s.decVal) :=
  rfl

/-- A `,` at end-of-input writes `0` to the current cell. -/
theorem step_read_nil (s : State) (h : s.input = []) :
    step [.read] s = some ([], { s with tape := fun i => if i = s.ptr then 0 else s.tape i }) := by
  rw [step, h]

/-- A `,` with available input writes it to the current cell and consumes it. -/
theorem step_read_cons (s : State) (x : Nat) (xs : List Nat) (h : s.input = x :: xs) :
    step [.read] s =
      some ([], { s with tape := fun i => if i = s.ptr then x else s.tape i, input := xs }) := by
  rw [step, h]

/-- A `.` appends the current value to the output. -/
theorem step_write (s : State) :
    step [.write] s = some ([], { s with output := s.currentVal :: s.output }) :=
  rfl

/-- A `[` with current value `0` skips its body. -/
theorem step_loop_zero (s : State) (body : Program) (h : State.currentVal s = 0) :
    step [.loop body] s = some ([], s) := by
  rw [step, if_pos h]

/-- A `[` with a non-zero current value runs its body and re-queues the loop. -/
theorem step_loop_nonzero (s : State) (body : Program) (h : State.currentVal s ≠ 0) :
    step [.loop body] s = some (body ++ [.loop body], s) := by
  rw [step, if_neg h, List.append_nil]

/-- Running for zero steps returns the state. -/
theorem run_zero (prog : Program) (s : State) : run 0 prog s = some s :=
  rfl

/-- The empty program halts immediately. -/
theorem run_empty (n : ℕ) (s : State) : run (n + 1) [] s = some s :=
  rfl

/-- The empty program takes zero steps to halt. -/
theorem stepsToHalt_empty (n : ℕ) (s : State) : stepsToHalt (n + 1) [] s = 0 :=
  rfl

/-- The empty program halts. -/
theorem halts_empty (s : State) : halts [] s := by
  exact ⟨1, by
    unfold haltsWithin
    rw [show stepsToHalt 1 [] s = 0 by rfl]
    decide⟩

/-- A non-empty program always has a step. -/
theorem step_cons_ne_none (i : Instruction) (rest : Program) (s : State) :
    step (i :: rest) s ≠ none := by
  cases i
  · intro h; simp only [step] at h; cases h
  · intro h; simp only [step] at h; cases h
  · intro h; simp only [step] at h; cases h
  · intro h; simp only [step] at h; cases h
  · intro h
    by_cases c : s.currentVal = 0
    · simp only [step, c] at h; cases h
    · simp only [step, c] at h; cases h
  · intro h
    rw [step] at h
    cases h_in : s.input with
    | nil => rw [h_in] at h; cases h
    | cons x xs => rw [h_in] at h; cases h
  · intro h; simp only [step] at h; cases h

/-- `stepsToHalt 1` is `0` exactly on the empty program. -/
theorem stepsToHalt_one_eq_zero (prog : Program) (s : State) :
    stepsToHalt 1 prog s = 0 ↔ prog = [] := by
  constructor
  · intro h
    unfold stepsToHalt at h
    cases hstep : step prog s with
    | none =>
        cases prog with
        | nil => rfl
        | cons i rest => exact False.elim (step_cons_ne_none i rest s hstep)
    | some cfg => simp only [hstep, stepsToHalt, Nat.zero_add] at h; cases h
  · intro h
    rw [h]
    rfl

-- divergence: [.loop [.inc_val]] from a non-zero cell never halts
theorem loop_incVal_stepsToHalt (s : State) (h : 0 < s.tape s.ptr) (n : Nat) :
    stepsToHalt n [.loop [.inc_val]] s = n := by
  have hmain : ∀ (n : Nat) (s : State), 0 < s.tape s.ptr →
      stepsToHalt n [.loop [.inc_val]] s = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro s hs
        have hcur : State.currentVal s ≠ 0 := by
          change s.tape s.ptr ≠ 0
          omega
        by_cases hn2 : n ≤ 1
        · cases n with
          | zero => rfl
          | succ n =>
              cases n with
              | zero =>
                  unfold stepsToHalt
                  rw [step_loop_nonzero s [.inc_val] hcur]
                  unfold stepsToHalt
                  rfl
              | succ n => omega
        · have hloop : step [.loop [.inc_val]] s =
              some ([.inc_val, .loop [.inc_val]], s) := by
            rw [step_loop_nonzero s [.inc_val] hcur]
            rfl
          have hinc : step [.inc_val, .loop [.inc_val]] s =
              some ([.loop [.inc_val]], s.incVal) := by
            rfl
          have hn' : n = (n - 2) + 2 := by omega
          rw [hn']
          simp only [stepsToHalt, hloop, hinc]
          have ih' := ih (n - 2) (by omega) s.incVal (by
            rw [incVal_ptr]
            simp only [State.incVal, State.modifyCell, if_true]
            omega)
          rw [ih']
  exact hmain n s h

theorem loop_incVal_never_halts (s : State) (h : 0 < s.tape s.ptr) :
    ¬ halts [.loop [.inc_val]] s := by
  intro hhalts
  rcases hhalts with ⟨n, hn⟩
  unfold haltsWithin at hn
  have hsteps := loop_incVal_stepsToHalt s h n
  rw [hsteps] at hn
  omega

-- echo: read then write
theorem read_write_echo (s : State) (x : Nat) (xs : List Nat) (h : s.input = x :: xs) :
    (runSeq [.read, .write] s).output = x :: s.output ∧ (runSeq [.read, .write] s).input = xs := by
  simp only [runSeq, stepOne, h, State.currentVal, if_true]
  constructor <;> trivial

-- writing twice appends two copies of the current value
theorem runSeq_write_write_output (s : State) :
    (runSeq [.write, .write] s).output = State.currentVal s :: State.currentVal s :: s.output := by
  rfl

-- read k times consumes the first k inputs
theorem runSeq_read_input (s : State) (k : Nat) (hk : k ≤ s.input.length) :
    (runSeq (List.replicate k .read) s).input = s.input.drop k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate, runSeq]
      cases hs : s.input with
      | nil =>
          rw [hs] at hk
          simp only [List.length_nil] at hk
          omega
      | cons x xs =>
          have hread : stepOne .read s =
              { s with input := xs, tape := fun i => if i = s.ptr then x else s.tape i } := by
            unfold stepOne
            rw [hs]
          rw [hread]
          let s' : State :=
            { s with input := xs, tape := fun i => if i = s.ptr then x else s.tape i }
          have ih' := ih s' (by
            rw [hs] at hk
            simp only [List.length_cons] at hk
            change k ≤ xs.length
            omega)
          rw [ih']
          rfl

end LeanBF
