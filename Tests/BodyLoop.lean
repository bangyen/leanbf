/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.BodyLoop

/-!
# Body Loop Tests

Kernel re-assertions of the `ifZeroElse` body-loop correctness machinery.
-/

namespace LeanBF.Tests

open LeanBF

example (test s : Int) (body : Program) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = 0) :
    RunsTo (bodyLoop test s body, s0) s0 :=
  runsTo_bodyLoop_zero test s body s0 hptr hv

example (w : Nat) (test s : Int) (body : Program) (s0 s1 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = w + 1)
    (hbody : RunsTo (body, { s0 with ptr := test }) s1) (h1ptr : s1.ptr = test) :
    RunsTo (bodyLoop test s body, s0)
      { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } :=
  runsTo_bodyLoop_succ w test s body s0 s1 hptr hv hbody h1ptr

example (test s : Int) (body : Program) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = 0) :
    ∃ fuel, RunsExactly fuel (bodyLoop test s body) s0 s0 :=
  run_bodyLoop_zero test s body s0 hptr hv

example (w : Nat) (test s : Int) (body : Program) (s0 s1 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = w + 1)
    (hbody : RunsTo (body, { s0 with ptr := test }) s1) (h1ptr : s1.ptr = test) :
    ∃ fuel, RunsExactly fuel (bodyLoop test s body) s0
      { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } :=
  run_bodyLoop_succ w test s body s0 s1 hptr hv hbody h1ptr

example (n k : Nat) (A B : Program) (s s' s'' : State)
    (hA : runToCompletion n A s = some s')
    (hB : runToCompletion k B s' = some s'') :
    runToCompletion (n + k) (A ++ B) s = some s'' :=
  runToCompletion_append n k A B s s' s'' hA hB

example (v : Nat) (s : State) (hv : s.tape s.ptr = v) :
    RunsTo (Compiler.clearHere, s)
      { s with tape := fun i => if i = s.ptr then 0 else s.tape i } :=
  runsTo_clearHere v s hv

example (fuel : Nat) (prog : Program) (s s' : State)
    (h : runToCompletion fuel prog s = some s') : RunsTo (prog, s) s' :=
  runsTo_of_runToCompletion_eq fuel prog s s' h

end LeanBF.Tests
