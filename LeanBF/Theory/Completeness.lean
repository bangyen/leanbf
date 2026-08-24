/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Compiler
import LeanBF.Core.Minsky
import LeanBF.Core.Semantics
import LeanBF.Core.State

/-!
# Turing Completeness

`turingCompleteness` is the statement that `Compiler.compileProgram`
simulates the two-counter Minsky machine. Its proof lives in
`Theory.Simulate.turingCompleteness_proof`.

## Main definitions

* `Simulates`: A Brainfuck state that simulates a Minsky state.
* `simState`: The canonical Brainfuck state that simulates a Minsky state.
* `HaltsWith`: A halted Brainfuck state holding a Minsky state's counters.
* `turingCompleteness`: The statement of Brainfuck Turing completeness.

## Theorems

* `simulates_simState`: `simState` indeed simulates its Minsky state.
-/

namespace LeanBF

/--
A Brainfuck state `bfs` simulates a Minsky state `ms` if:
1. `bfs.ptr` is at the `running` cell (0).
2. `bfs.tape 1` is `ms.pc`.
3. `bfs.tape 2` is `ms.c1`.
4. `bfs.tape 3` is `ms.c2`.
5. `bfs.tape 0` is 1 (running).
-/
def Simulates (ms : Minsky.State) (bfs : State) : Prop :=
  bfs.ptr = 0 ∧
  bfs.tape 1 = ms.pc ∧
  bfs.tape 2 = ms.c1 ∧
  bfs.tape 3 = ms.c2 ∧
  bfs.tape 0 = 1

/--
The canonical simulating state for `ms`: the `running` flag is set, `pc`/`c1`/
`c2` are in cells 1-3, and every other cell is `0`.
-/
def simState (ms : Minsky.State) : State :=
  { ptr := 0,
    tape := fun i =>
      if i = 0 then 1 else
      if i = 1 then ms.pc else
      if i = 2 then ms.c1 else
      if i = 3 then ms.c2 else 0,
    input := [], output := [] }

/-- `simState` indeed simulates its Minsky state. -/
theorem simulates_simState (ms : Minsky.State) : Simulates ms (simState ms) := by
  unfold Simulates simState
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

/--
A Brainfuck state `bfs` is a halted state holding the counters of the Minsky
state `ms`: the pointer is back at the `running` cell, the running flag is
cleared, and `c1`/`c2` sit in cells 2 and 3. The `pc` is not constrained, as
the dispatch loop zeroes it on halting.
-/
def HaltsWith (ms : Minsky.State) (bfs : State) : Prop :=
  bfs.ptr = 0 ∧ bfs.tape 0 = 0 ∧ bfs.tape 2 = ms.c1 ∧ bfs.tape 3 = ms.c2

/--
The statement of Brainfuck Turing completeness: for every Minsky machine `m`,
the compiled Brainfuck program `Compiler.compileProgram m` halts whenever `m`
does, starting from the canonical simulating state `simState ms`, and the
halting state holds `m`'s final counters. This is `HaltsWith` rather than
`Simulates ms_final`: at a terminal state the dispatch loop clears the running
flag, so `bfs_final.tape 0` is `0` where `Simulates` demands `1`.
-/
def turingCompleteness : Prop :=
  ∀ (m : Minsky.Program),
    ∀ (ms ms_final : Minsky.State),
      Minsky.RunsTo m ms ms_final →
      ∃ (bfs_final : State), RunsTo (Compiler.compileProgram m, simState ms) bfs_final ∧
        HaltsWith ms_final bfs_final

end LeanBF
