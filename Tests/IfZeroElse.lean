/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.IfZeroElse

/-!
# `ifZeroElse` Tests

Kernel re-assertions of the `ifZeroElse` conditional correctness machinery.
-/

namespace LeanBF.Tests

open LeanBF

example (test s1 s2 s4 : Int) (a b c v : Nat) (s : State)
    (hptr : s.ptr = test) (hv : s.tape test = v) (h1 : s.tape s1 = a)
    (h2 : s.tape s2 = b) (h4 : s.tape s4 = c)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s4 ∧ s1 ≠ s2 ∧ s1 ≠ s4 ∧ s2 ≠ s4) :
    RunsTo (copyLoop test s1 s2 s4, s) (copyLoopPost test s1 s2 s4 a b c v s) :=
  runsTo_copyLoop v test s1 s2 s4 a b c s hptr hv h1 h2 h4 hsep

example (v w : Nat) (s1 s3 : Int) (s : State) (hsep : s1 ≠ s3) :
    s.ptr = s1 → s.tape s1 = v → s.tape s3 = w →
      RunsTo (flagLoop s1 s3, s) (flagLoopPost s1 s3 w v s) := by
  intro hptr hv hw
  exact runsTo_flagLoop v w s1 s3 s hptr hv hw hsep

example (test s1 s2 s3 s4 : Int) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4) :
    RunsTo (ifZeroElseSetup test s1 s2 s3 s4, s0) (thenBodyState test s1 s2 s3 s4 s0) :=
  runsTo_setup_zero test s1 s2 s3 s4 s0 hptr hv hsep

example (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program) (s0 s_then : State)
    (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    RunsTo (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) :=
  runsTo_ifZeroElse_zero test s1 s2 s3 s4 thenBody elseBody s0 s_then hptr hv hsep hthen h1 h2 h3 h4

example (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program) (s0 s_then : State)
    (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    ∃ fuel, RunsExactly fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) :=
  run_ifZeroElse_zero test s1 s2 s3 s4 thenBody elseBody s0 s_then hptr hv hsep hthen h1 h2 h3 h4

end LeanBF.Tests
