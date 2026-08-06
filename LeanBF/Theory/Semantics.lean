/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics

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

end LeanBF
