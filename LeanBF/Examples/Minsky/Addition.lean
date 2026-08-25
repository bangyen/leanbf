/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Simulate
import LeanBF.Theory.Simulation

/-!
# Addition Minsky Machine

A concrete two-counter Minsky machine that adds its first counter into its
second: each unit of `c1` is decremented and re-added to `c2`, so the machine
halts with `c1 = 0` and `c2 := c1 + c2`.

Unlike `CountDown` and `Quadruple`, whose effects on `c2` are fixed multiples
built into the program structure, this machine's result depends on both
counters. That is the limit of what two counters express directly: a general
multiplication `c2 := c1 * c2` needs three quantities live at once (the
counter, the multiplicand, and the accumulator) and so requires a Godel
encoding of two values into one register.

## Main definitions

* `addMachine`: The Minsky program.
* `addStart`: The initial state (`c1 = 2`, `c2 = 3`).
* `addFinal`: The final state (`c1 = 0`, `c2 = 5`).

## Theorems

* `add_runs`: The Minsky machine runs from `addStart` to the final state.
* `add_compiled`: The compiled program halts and leaves the final counter
  values on the tape.
* `add_halts`: The compiled program halts from the canonical state.
* `add_executes`: The interpreter's `run` completes the compiled program in
  exactly n steps with `c2 = 5` on the tape.
-/

namespace LeanBF.Examples

open LeanBF.Minsky

/--
The program `jzdec1 2 1; inc2 0; halt`: while `c1` is non-zero, decrement it
and increment `c2`; when `c1` reaches zero, jump to `halt`.
-/
def addMachine : Minsky.Program :=
  [.jzdec1 2 1, .inc2 0, .halt]

/-- The initial state: `c1 = 2`, `c2 = 3`. -/
def addStart : Minsky.State :=
  { pc := 0, c1 := 2, c2 := 3 }

/-- The final state: `c1 = 0`, `c2 = 5 = 2 + 3`, pointing at `halt`. -/
def addFinal : Minsky.State :=
  { pc := 2, c1 := 0, c2 := 5 }

/-- The Minsky machine runs from `addStart` to `addFinal`. -/
theorem add_runs : Minsky.RunsTo addMachine addStart addFinal := by
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
program counter (0), cell 2 holds `c1 = 0`, and cell 3 holds `c2 = 5`.
-/
theorem add_compiled : ∃ s',
    RunsTo (Compiler.compileProgram addMachine, simState addStart) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 5 := by
  have hsim : SimulatesAt addStart 0 (simState addStart) := by
    simpa only [SimulatesAt, Simulates] using simulates_simState addStart
  have hclean : (simState addStart).tape 5 = 0 ∧ (simState addStart).tape 6 = 0 ∧
      (simState addStart).tape 7 = 0 ∧ (simState addStart).tape 8 = 0 := by
    refine ⟨rfl, rfl, rfl, rfl⟩
  rcases runsTo_compileProgram addMachine addStart addFinal (simState addStart)
    add_runs hsim hclean with ⟨s', hrun, hpost⟩
  have hm : dispatchMs addMachine addFinal = { addFinal with pc := 0 } :=
    (dispatch_halt addMachine addFinal (by rfl)).2.2
  refine ⟨s', hrun, hpost.1, hpost.2.1, ?_, ?_, ?_⟩
  · rw [hpost.2.2.1, hm]
  · rw [hpost.2.2.2.1, hm]
    rfl
  · rw [hpost.2.2.2.2, hm]
    rfl

/-- The compiled program halts, starting from the canonical simulating state. -/
theorem add_halts :
    ∃ s', RunsTo (Compiler.compileProgram addMachine, simState addStart) s' := by
  rcases add_compiled with ⟨s', hrun, _⟩
  exact ⟨s', hrun⟩

/--
The interpreter's `run` completes the compiled program, halting in exactly
`n` steps with the pointer back at 0, the running flag cleared, the program
counter reset, `c1 = 0`, and `c2 = 5`.
-/
theorem add_executes :
    ∃ n s', run n (Compiler.compileProgram addMachine) (simState addStart) = some s' ∧
      stepsToHalt (n + 1) (Compiler.compileProgram addMachine) (simState addStart) = n ∧
        s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 5 := by
  rcases add_compiled with ⟨s', hrun, hpost⟩
  rcases run_of_RunsTo (Compiler.compileProgram addMachine, simState addStart) s' hrun
    with ⟨n, hex, hsteps⟩
  exact ⟨n, s', hex, hsteps, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2⟩

end LeanBF.Examples
