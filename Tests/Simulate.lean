/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Simulate

/-!
# Dispatch Simulation Tests

Kernel re-assertions of the dispatch simulation and the Turing completeness
statement.
-/

namespace LeanBF.Tests

open LeanBF

example : turingCompleteness :=
  turingCompleteness_proof

/-- The completeness statement delivers the final counters, not just halting. -/
example (ms ms_final : Minsky.State)
    (h : Minsky.RunsTo [Minsky.Instruction.halt] ms ms_final) :
    ∃ bfs, RunsTo (Compiler.compileProgram [Minsky.Instruction.halt], simState ms) bfs ∧
      bfs.tape 2 = ms_final.c1 ∧ bfs.tape 3 = ms_final.c2 := by
  rcases turingCompleteness_proof [Minsky.Instruction.halt] ms ms_final h with
    ⟨b, hr, _, _, h1, h2⟩
  exact ⟨b, hr, h1, h2⟩

example (m : Minsky.Program) (ms ms' : Minsky.State) (s : State)
    (hr : Minsky.RunsTo m ms ms') (hsim : SimulatesAt ms 0 s)
    (hclean : s.tape 5 = 0 ∧ s.tape 6 = 0 ∧ s.tape 7 = 0 ∧ s.tape 8 = 0) :
    ∃ s', RunsTo (Compiler.compileProgram m, s) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧
        s'.tape 1 = (dispatchMs m ms').pc ∧ s'.tape 2 = (dispatchMs m ms').c1 ∧
        s'.tape 3 = (dispatchMs m ms').c2 :=
  runsTo_compileProgram m ms ms' s hr hsim hclean

end LeanBF.Tests
