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

## Main definitions

* `Simulates`: A Brainfuck state that simulates a Minsky state.
* `turingCompleteness`: The statement of Brainfuck Turing completeness.

`turingCompleteness` is currently an open conjecture, not a theorem: proving
it is the project's main goal (see the Roadmap in the README).
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
The statement of Brainfuck Turing completeness: for every Minsky machine `m`,
there exists a Brainfuck program `bf` such that if `m` halts from an initial
state, `bf` also halts from a simulating initial state.

This is a conjecture, not a theorem: the proof is open work (see the Roadmap
in the README).
-/
def turingCompleteness : Prop :=
  ∀ (m : Minsky.Program),
    ∃ (bf : Program),
      ∀ (ms ms_final : Minsky.State) (bfs : State),
        Simulates ms bfs →
        Minsky.RunsTo m ms ms_final →
        ∃ (bfs_final : State), RunsTo (bf, bfs) bfs_final

end LeanBF
