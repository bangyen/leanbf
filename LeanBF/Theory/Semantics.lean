/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics

/-!
# Semantics Lemmas

Single-step behavior of the interpreter on the empty program, pointer
movement, and the loop instruction.

## Theorems

* `step_empty`: The empty program has no step.
* `step_incPtr`: A single `>` moves the pointer.
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
