/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Simulate
import LeanBF.Theory.Simulation

/-!
# Tripler Minsky Machine

A concrete two-counter Minsky machine that triples its second counter: phase
one transfers `c2` into `c1` one unit at a time, and phase two transfers `c1`
back into `c2` adding three units per unit, so the machine halts with
`c1 = 0` and `c2 := 3 * c2`.

This is the odd-multiplier companion to `Quadruple`, whose two phases both
double. The multiplier lives in the program structure rather than in the
counters, which is what makes constant multiples expressible with only two
registers.

## Main definitions

* `tripler`: The Minsky program.
* `triplerStart`: The initial state (counter 2 holds 2).
* `triplerFinal`: The final state (counter 2 holds 6).

## Theorems

* `tripler_runs`: The Minsky machine runs from `triplerStart` to the final
  state.
* `tripler_compiled`: The compiled program halts and leaves the final counter
  values on the tape.
* `tripler_halts`: The compiled program halts from the canonical state.
* `tripler_executes`: The interpreter's `run` completes the compiled program
  in exactly n steps with `c2 = 6` on the tape.
-/

namespace LeanBF.Examples

open LeanBF.Minsky

/--
The program `jzdec2 2 1; inc1 0; jzdec1 6 3; inc2 4; inc2 5; inc2 2; halt`:
phase one drains `c2` into `c1`, and phase two drains `c1` back into `c2`
three units at a time.
-/
def tripler : Minsky.Program :=
  [.jzdec2 2 1, .inc1 0, .jzdec1 6 3, .inc2 4, .inc2 5, .inc2 2, .halt]

/-- The initial state: `c2 = 2`, `c1 = 0`. -/
def triplerStart : Minsky.State :=
  { pc := 0, c1 := 0, c2 := 2 }

/-- The final state: `c2 = 6 = 3 * 2`, `c1 = 0`, pointing at `halt`. -/
def triplerFinal : Minsky.State :=
  { pc := 6, c1 := 0, c2 := 6 }

/-- The Minsky machine runs from `triplerStart` to `triplerFinal`. -/
theorem tripler_runs : Minsky.RunsTo tripler triplerStart triplerFinal := by
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
                            · apply Minsky.RunsTo.halt
                              left
                              rfl

/--
The compiled program halts, and on the final tape cell 1 holds the reset
program counter (0), cell 2 holds `c1 = 0`, and cell 3 holds `c2 = 6`.
-/
theorem tripler_compiled : ∃ s',
    RunsTo (Compiler.compileProgram tripler, simState triplerStart) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 6 := by
  have hsim : SimulatesAt triplerStart 0 (simState triplerStart) := by
    simpa only [SimulatesAt, Simulates] using simulates_simState triplerStart
  have hclean : (simState triplerStart).tape 5 = 0 ∧ (simState triplerStart).tape 6 = 0 ∧
      (simState triplerStart).tape 7 = 0 ∧ (simState triplerStart).tape 8 = 0 := by
    refine ⟨rfl, rfl, rfl, rfl⟩
  rcases runsTo_compileProgram tripler triplerStart triplerFinal (simState triplerStart)
    tripler_runs hsim hclean with ⟨s', hrun, hpost⟩
  have hm : dispatchMs tripler triplerFinal = { triplerFinal with pc := 0 } :=
    (dispatch_halt tripler triplerFinal (by rfl)).2.2
  refine ⟨s', hrun, hpost.1, hpost.2.1, ?_, ?_, ?_⟩
  · rw [hpost.2.2.1, hm]
  · rw [hpost.2.2.2.1, hm]
    rfl
  · rw [hpost.2.2.2.2, hm]
    rfl

/-- The compiled program halts, starting from the canonical simulating state. -/
theorem tripler_halts :
    ∃ s', RunsTo (Compiler.compileProgram tripler, simState triplerStart) s' := by
  rcases tripler_compiled with ⟨s', hrun, _⟩
  exact ⟨s', hrun⟩

/--
The interpreter's `run` completes the compiled program, halting in exactly
`n` steps with the pointer back at 0, the running flag cleared, the program
counter reset, `c1 = 0`, and `c2 = 6`.
-/
theorem tripler_executes :
    ∃ n s', run n (Compiler.compileProgram tripler) (simState triplerStart) = some s' ∧
      stepsToHalt (n + 1) (Compiler.compileProgram tripler) (simState triplerStart) = n ∧
        s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 6 := by
  rcases tripler_compiled with ⟨s', hrun, hpost⟩
  rcases run_of_RunsTo (Compiler.compileProgram tripler, simState triplerStart) s' hrun
    with ⟨n, hex, hsteps⟩
  exact ⟨n, s', hex, hsteps, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2⟩

end LeanBF.Examples
