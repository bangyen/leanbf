/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Simulate
import LeanBF.Theory.Simulation

/-!
# Count-Down Minsky Machine

A concrete two-counter Minsky machine that decrements its first counter to
zero, counting each step in the second counter, and then halts. This example
runs the machine through `runsTo_compileProgram` and shows that the compiled
Brainfuck program halts on the canonical simulating state, leaving the
final counter values on the tape.

## Main definitions

* `countDown`: The Minsky program.
* `countDownStart`: The initial state (counter 1 holds 2).
* `countDownFinal`: The final state (counter 1 is 0, counter 2 holds 2).

## Theorems

* `countDown_runs`: The Minsky machine runs from `countDownStart` to
  the final state.
* `countDown_compiled`: The compiled program halts and leaves the final
  counter values on the tape.
* `countDown_halts`: The compiled program halts from the canonical state.
* `countDown_executes`: The interpreter's `run` completes the compiled
  program in exactly n steps with `c2 = 2` on the tape.
-/

namespace LeanBF.Examples

open LeanBF.Minsky

/--
The program `jzdec1 2 1; inc2 0; halt`: while `c1` is non-zero, decrement it
and increment `c2`; once `c1` reaches zero, halt.
-/
def countDown : Minsky.Program :=
  [.jzdec1 2 1, .inc2 0, .halt]

/-- The initial state: `c1 = 2`, `c2 = 0`. -/
def countDownStart : Minsky.State :=
  { pc := 0, c1 := 2, c2 := 0 }

/-- The final state: `c1 = 0`, `c2 = 2`, pointing at `halt`. -/
def countDownFinal : Minsky.State :=
  { pc := 2, c1 := 0, c2 := 2 }

/-- The Minsky machine runs from `countDownStart` to `countDownFinal`. -/
theorem countDown_runs : Minsky.RunsTo countDown countDownStart countDownFinal := by
  apply Minsky.RunsTo.step
  · rfl
  · apply Minsky.RunsTo.step
    · rfl
    · apply Minsky.RunsTo.step
      · rfl
      · apply Minsky.RunsTo.step
        · rfl
        · apply Minsky.RunsTo.step
          · rfl
          · apply Minsky.RunsTo.halt
            left
            rfl

/--
The compiled program halts, and on the final tape cell 1 holds the reset
program counter (0), cell 2 holds `c1 = 0`, and cell 3 holds `c2 = 2`.
-/
theorem countDown_compiled : ∃ s',
    RunsTo (Compiler.compileProgram countDown, simState countDownStart) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 2 := by
  have hsim : SimulatesAt countDownStart 0 (simState countDownStart) := by
    simpa only [SimulatesAt, Simulates] using simulates_simState countDownStart
  have hclean : (simState countDownStart).tape 5 = 0 ∧ (simState countDownStart).tape 6 = 0 ∧
      (simState countDownStart).tape 7 = 0 ∧ (simState countDownStart).tape 8 = 0 := by
    constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl
  have hsimRun :=
    runsTo_compileProgram countDown countDownStart countDownFinal (simState countDownStart)
      countDown_runs hsim hclean
  rcases hsimRun with ⟨s', hrun, hpost⟩
  have hm : dispatchMs countDown countDownFinal = { countDownFinal with pc := 0 } :=
    (dispatch_halt countDown countDownFinal (by rfl)).2.2
  have h1 : s'.tape 1 = 0 := by
    rw [hpost.2.2.1, hm]
  have h2 : s'.tape 2 = 0 := by
    rw [hpost.2.2.2.1, hm]
    rfl
  have h3 : s'.tape 3 = 2 := by
    rw [hpost.2.2.2.2, hm]
    rfl
  exact ⟨s', hrun, hpost.1, hpost.2.1, h1, h2, h3⟩

/-- The compiled program halts, starting from the canonical simulating state. -/
theorem countDown_halts :
    ∃ s', RunsTo (Compiler.compileProgram countDown, simState countDownStart) s' := by
  rcases countDown_compiled with ⟨s', hrun, hpost⟩
  exact ⟨s', hrun⟩

/--
The interpreter's `run` completes the compiled program, halting in exactly
`n` steps with the pointer back at 0, the running flag cleared, the program
counter reset, `c1 = 0`, and `c2 = 2`.
-/
theorem countDown_executes :
    ∃ n s', run n (Compiler.compileProgram countDown) (simState countDownStart) = some s' ∧
      stepsToHalt (n + 1) (Compiler.compileProgram countDown) (simState countDownStart) = n ∧
        s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 2 := by
  rcases countDown_compiled with ⟨s', hrun, hpost⟩
  rcases run_of_RunsTo (Compiler.compileProgram countDown, simState countDownStart) s' hrun
    with ⟨n, hex, hsteps⟩
  exact ⟨n, s', hex, hsteps, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2⟩

end LeanBF.Examples
