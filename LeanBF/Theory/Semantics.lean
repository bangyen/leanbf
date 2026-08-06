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

end LeanBF
