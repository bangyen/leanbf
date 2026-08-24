/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Simulate

/-!
# Completeness Converse Tests

Kernel re-assertions of the converse: a halting compiled Brainfuck run
implies the source Minsky machine halts.
-/

namespace LeanBF.Tests

open LeanBF

example (m : Minsky.Program) (ms : Minsky.State) (bfs : State)
    (h : RunsTo (Compiler.compileProgram m, simState ms) bfs) :
    ∃ ms_final, Minsky.RunsTo m ms ms_final :=
  minsky_halts_of_compiled_halts m ms bfs h

/-- On a concrete machine, a halting compiled run yields a Minsky run. -/
example (bfs : State)
    (h : RunsTo (Compiler.compileProgram [Minsky.Instruction.halt],
      simState { pc := 0, c1 := 3, c2 := 4 }) bfs) :
    ∃ ms_final, Minsky.RunsTo [Minsky.Instruction.halt]
      { pc := 0, c1 := 3, c2 := 4 } ms_final :=
  minsky_halts_of_compiled_halts _ _ bfs h

/-- A non-terminal program counter always steps. -/
example (m : Minsky.Program) (ms : Minsky.State)
    (h : ¬((m : List Minsky.Instruction)[ms.pc]? = some .halt ∨
           (m : List Minsky.Instruction)[ms.pc]? = none)) :
    ∃ ms', Minsky.step m ms = some ms' :=
  minsky_step_isSome m ms h

end LeanBF.Tests
