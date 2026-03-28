import LeanBF.Basic
import LeanBF.Semantics
import LeanBF.Minsky
import LeanBF.Compiler

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
Main Theorem: For every Minsky Machine `m`, there exists a Brainfuck program `bf`
such that if `m` halts from an initial state, `bf` also halts from a simulating initial state.
-/
theorem turing_completeness (m : Minsky.Program) :
  ∃ (bf : Program),
    ∀ (ms ms_final : Minsky.State) (bfs : State),
      Simulates ms bfs →
      Minsky.RunsTo m ms ms_final →
      ∃ (bfs_final : State), RunsTo (bf, bfs) bfs_final := by
  sorry

end LeanBF
