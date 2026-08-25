/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Simulate
import LeanBF.Theory.Simulation

/-!
# Quadruple Minsky Machine

A concrete two-counter Minsky machine that quadruples its second counter:
phase one transfers `c2` into `c1`, adding twice per unit (so `c1 := 2 * c2`),
and phase two transfers `c1` back into `c2`, adding twice per unit (so
`c2 := 4 * c2`), after which the machine halts with `c1 = 0`. Unlike
`CountDown`, this machine exercises every instruction (`jzdec1`, `jzdec2`,
`inc1`, `inc2`, `halt`) and runs it through `runsTo_compileProgram`.

## Main definitions

* `quadruple`: The Minsky program.
* `quadrupleStart`: The initial state (counter 2 holds 2).
* `quadrupleFinal`: The final state (counter 2 holds 8).

## Theorems

* `quadruple_runs`: The Minsky machine runs from `quadrupleStart` to
  the final state.
* `quadruple_compiled`: The compiled program halts and leaves the final
  counter values on the tape.
* `quadruple_halts`: The compiled program halts from the canonical state.
* `quadruple_executes`: The interpreter's `run` completes the compiled
  program in exactly n steps with `c2 = 8` on the tape.
-/

namespace LeanBF.Examples

open LeanBF.Minsky

/--
The program `jzdec2 3 1; inc1 2; inc1 0; jzdec1 6 4; inc2 5; inc2 3; halt`:
phase one transfers `c2` into `c1` adding twice per unit, phase two transfers
`c1` back into `c2` adding twice per unit, then the machine halts.
-/
def quadruple : Minsky.Program :=
  [.jzdec2 3 1, .inc1 2, .inc1 0, .jzdec1 6 4, .inc2 5, .inc2 3, .halt]

/-- The initial state: `c2 = 2`, `c1 = 0`. -/
def quadrupleStart : Minsky.State :=
  { pc := 0, c1 := 0, c2 := 2 }

/-- The final state: `c2 = 8 = 4 * 2`, `c1 = 0`, pointing at `halt`. -/
def quadrupleFinal : Minsky.State :=
  { pc := 6, c1 := 0, c2 := 8 }

/-- The Minsky machine runs from `quadrupleStart` to `quadrupleFinal`. -/
theorem quadruple_runs : Minsky.RunsTo quadruple quadrupleStart quadrupleFinal := by
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
          · apply Minsky.RunsTo.step
            · rfl
            · apply Minsky.RunsTo.step
              · rfl
              · apply Minsky.RunsTo.step
                · rfl
                · apply Minsky.RunsTo.step
                  · rfl
                  · apply Minsky.RunsTo.step
                    · rfl
                    · apply Minsky.RunsTo.step
                      · rfl
                      · apply Minsky.RunsTo.step
                        · rfl
                        · apply Minsky.RunsTo.step
                          · rfl
                          · apply Minsky.RunsTo.step
                            · rfl
                            · apply Minsky.RunsTo.step
                              · rfl
                              · apply Minsky.RunsTo.step
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
program counter (0), cell 2 holds `c1 = 0`, and cell 3 holds `c2 = 8`.
-/
theorem quadruple_compiled : ∃ s',
    RunsTo (Compiler.compileProgram quadruple, simState quadrupleStart) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 8 := by
  have hsim : SimulatesAt quadrupleStart 0 (simState quadrupleStart) := by
    simpa only [SimulatesAt, Simulates] using simulates_simState quadrupleStart
  have hclean : (simState quadrupleStart).tape 5 = 0 ∧ (simState quadrupleStart).tape 6 = 0 ∧
      (simState quadrupleStart).tape 7 = 0 ∧ (simState quadrupleStart).tape 8 = 0 := by
    constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl
  have hsimRun :=
    runsTo_compileProgram quadruple quadrupleStart quadrupleFinal (simState quadrupleStart)
      quadruple_runs hsim hclean
  rcases hsimRun with ⟨s', hrun, hpost⟩
  have hm : dispatchMs quadruple quadrupleFinal = { quadrupleFinal with pc := 0 } :=
    (dispatch_halt quadruple quadrupleFinal (by rfl)).2.2
  have h1 : s'.tape 1 = 0 := by
    rw [hpost.2.2.1, hm]
  have h2 : s'.tape 2 = 0 := by
    rw [hpost.2.2.2.1, hm]
    rfl
  have h3 : s'.tape 3 = 8 := by
    rw [hpost.2.2.2.2, hm]
    rfl
  exact ⟨s', hrun, hpost.1, hpost.2.1, h1, h2, h3⟩

/-- The compiled program halts, starting from the canonical simulating state. -/
theorem quadruple_halts :
    ∃ s', RunsTo (Compiler.compileProgram quadruple, simState quadrupleStart) s' := by
  rcases quadruple_compiled with ⟨s', hrun, hpost⟩
  exact ⟨s', hrun⟩

/--
The interpreter's `run` completes the compiled program, halting in exactly
`n` steps with the pointer back at 0, the running flag cleared, the program
counter reset, `c1 = 0`, and `c2 = 8`.
-/
theorem quadruple_executes :
    ∃ n s', run n (Compiler.compileProgram quadruple) (simState quadrupleStart) = some s' ∧
      stepsToHalt (n + 1) (Compiler.compileProgram quadruple) (simState quadrupleStart) = n ∧
        s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 8 := by
  rcases quadruple_compiled with ⟨s', hrun, hpost⟩
  rcases run_of_RunsTo (Compiler.compileProgram quadruple, simState quadrupleStart) s' hrun
    with ⟨n, hex, hsteps⟩
  exact ⟨n, s', hex, hsteps, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2⟩

end LeanBF.Examples
