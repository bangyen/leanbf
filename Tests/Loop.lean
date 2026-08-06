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

example (s : State) (hptr : s.ptr = (0 : Int)) :
    (runSeq (Compiler.movePtr 0 3) s).ptr = 3 :=
  runSeq_movePtr_ptr 0 3 s hptr

example (i j : Int) (s : State) :
    (runSeq (Compiler.movePtr i j) s).tape = s.tape :=
  runSeq_movePtr_tape i j s

example (n : Nat) (s : State) :
    (runSeq (List.replicate n .inc_ptr) s).ptr = s.ptr + (n : Int) :=
  runSeq_replicate_inc_ptr n s

example : let s : State :=
      { ptr := 2,
        tape := fun i =>
          if i = 2 then 3 else
          if i = 5 then 1 else
          if i = 6 then 2 else
          if i = 8 then 4 else 0,
        input := [], output := [] }
    ; ∃ n : Nat, run n (copyLoop 2 5 6 8) s = some (copyLoopPost 2 5 6 8 1 2 4 3 s) := by
  let s : State :=
    { ptr := 2,
      tape := fun i =>
        if i = 2 then 3 else
        if i = 5 then 1 else
        if i = 6 then 2 else
        if i = 8 then 4 else 0,
      input := [], output := [] }
  exact run_copyLoop 3 2 5 6 8 1 2 4 s rfl rfl rfl rfl rfl (by decide)

end LeanBF.Tests
