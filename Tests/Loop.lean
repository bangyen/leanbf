/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Loop

/-!
# Loop Tests

Kernel re-assertions of the loop-correctness machinery.
-/

namespace LeanBF.Tests

open LeanBF

example (A : Program) (s : State) :
    LoopFree A → run A.length A s = some (runSeq A s) :=
  run_length_loop_free A s

example (n : Nat) (A B : Program) (s : State) :
    LoopFree A → run (A.length + n) (A ++ B) s = run n B (runSeq A s) :=
  run_append n A B s

example : LoopFree (Compiler.movePtr 0 3) :=
  loop_free_movePtr 0 3

example : LoopFree (Compiler.movePtr 5 2) :=
  loop_free_movePtr 5 2

example (A B : Program) :
    LoopFree A → LoopFree B → LoopFree (A ++ B) :=
  loop_free_append A B

end LeanBF.Tests
