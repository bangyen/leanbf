/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Semantics
import LeanBF.Theory.BodyLoop
import LeanBF.Theory.IfZeroElse.Setup

/-!
# ifZeroElse

The `Compiler.ifZeroElse` conditional itself: a zero tested cell runs
`thenBody` exactly once and a non-zero one runs `elseBody` exactly once,
preserving the tested cell and restoring the scratch cells, in `RunsTo`,
`run`, and fuel-capped form.

## Theorems

* `runsTo_ifZeroElse_zero`: A zero tested cell runs `thenBody` exactly once.
* `runsTo_ifZeroElse_succ`: A non-zero tested cell runs `elseBody` exactly
  once.
* `run_ifZeroElse_zero`/`run_ifZeroElse_succ`: The run forms.
* `runToCompletion_ifZeroElse_zero`/`runToCompletion_ifZeroElse_succ`: The
  fuel-capped forms.
-/

namespace LeanBF

/-- A zero tested cell runs `thenBody` exactly once, and the scratch cells are
    restored to `0`. -/
theorem runsTo_ifZeroElse_zero (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_then : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    RunsTo (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
  rcases hsep with ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
  have it1 : (test : Int) ≠ (s1 : Int) := fun h => ht1 (Int.ofNat.inj h)
  have it2 : (test : Int) ≠ (s2 : Int) := fun h => ht2 (Int.ofNat.inj h)
  have it3 : (test : Int) ≠ (s3 : Int) := fun h => ht3 (Int.ofNat.inj h)
  have it4 : (test : Int) ≠ (s4 : Int) := fun h => ht4 (Int.ofNat.inj h)
  have i12 : (s1 : Int) ≠ (s2 : Int) := fun h => h12 (Int.ofNat.inj h)
  have i13 : (s1 : Int) ≠ (s3 : Int) := fun h => h13 (Int.ofNat.inj h)
  have i14 : (s1 : Int) ≠ (s4 : Int) := fun h => h14 (Int.ofNat.inj h)
  have i23 : (s2 : Int) ≠ (s3 : Int) := fun h => h23 (Int.ofNat.inj h)
  have i24 : (s2 : Int) ≠ (s4 : Int) := fun h => h24 (Int.ofNat.inj h)
  have i34 : (s3 : Int) ≠ (s4 : Int) := fun h => h34 (Int.ofNat.inj h)
  let sT : State := thenBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0
  have hSetup : RunsTo
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0) sT := by
    have hs : RunsTo (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0)
        (thenBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0) :=
      runsTo_setup_zero (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0 hptr hv
        ⟨it1, it2, it3, it4, i12, i13, i14, i23, i24, i34⟩
    simpa only [sT] using hs
  have hsTptr : sT.ptr = (test : Int) := by simp only [sT, thenBodyState]
  have hsTzero : sT.tape (s2 : Int) = 0 := by
    simp only [sT, thenBodyState]
    rw [if_neg (Ne.symm it2), if_neg (Ne.symm i12), if_true]
  have hsTone : sT.tape (s3 : Int) = 0 + 1 := by
    simp only [sT, thenBodyState]
    rw [if_neg (Ne.symm it3), if_neg (Ne.symm i13), if_neg (Ne.symm i23), if_true]
  have hSkip : RunsTo (bodyLoop (test : Int) (s2 : Int) elseBody, sT) sT :=
    runsTo_bodyLoop_zero (test : Int) (s2 : Int) elseBody sT hsTptr hsTzero
  have hThen : RunsTo (bodyLoop (test : Int) (s3 : Int) thenBody, sT)
      { s_then with
        ptr := (test : Int), tape := fun i => if i = (s3 : Int) then 0 else s_then.tape i } :=
    runsTo_bodyLoop_succ 0 (test : Int) (s3 : Int) thenBody sT s_then hsTptr hsTone hthen h1
  have hprog : Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody =
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) ++
        bodyLoop (test : Int) (s2 : Int) elseBody ++ bodyLoop (test : Int) (s3 : Int) thenBody) :=
    ifZeroElse_eq_chain test s1 s2 s3 s4 thenBody elseBody
  have hThen' : RunsTo (bodyLoop (test : Int) (s3 : Int) thenBody, sT)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
    rw [thenPost_eq test s1 s2 s3 s4 s_then h2 h3 h4 i12 i13 i14 i23 i24 i34] at hThen
    exact hThen
  have hchain :=
    (RunsTo_append (bodyLoop (test : Int) (s3 : Int) thenBody) sT
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then)
      (RunsTo_append (bodyLoop (test : Int) (s2 : Int) elseBody) sT sT hSetup hSkip)
      hThen')
  exact RunsTo_eq_program hchain hprog.symm

/-- A non-zero tested cell runs `elseBody` exactly once, and the scratch cells
    are restored to `0`. -/
theorem runsTo_ifZeroElse_succ (w : Nat) (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_else : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = w + 1)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (helse : RunsTo (elseBody, elseBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) (w + 1) s0) s_else)
    (h1 : s_else.ptr = (test : Int)) (h2 : s_else.tape s1 = 0)
    (h3 : s_else.tape s3 = 0) (h4 : s_else.tape s4 = 0) :
    RunsTo (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
  rcases hsep with ⟨ht1, ht2, ht3, ht4, h12, h13, h14, h23, h24, h34⟩
  have it1 : (test : Int) ≠ (s1 : Int) := fun h => ht1 (Int.ofNat.inj h)
  have it2 : (test : Int) ≠ (s2 : Int) := fun h => ht2 (Int.ofNat.inj h)
  have it3 : (test : Int) ≠ (s3 : Int) := fun h => ht3 (Int.ofNat.inj h)
  have it4 : (test : Int) ≠ (s4 : Int) := fun h => ht4 (Int.ofNat.inj h)
  have i12 : (s1 : Int) ≠ (s2 : Int) := fun h => h12 (Int.ofNat.inj h)
  have i13 : (s1 : Int) ≠ (s3 : Int) := fun h => h13 (Int.ofNat.inj h)
  have i14 : (s1 : Int) ≠ (s4 : Int) := fun h => h14 (Int.ofNat.inj h)
  have i23 : (s2 : Int) ≠ (s3 : Int) := fun h => h23 (Int.ofNat.inj h)
  have i24 : (s2 : Int) ≠ (s4 : Int) := fun h => h24 (Int.ofNat.inj h)
  have i34 : (s3 : Int) ≠ (s4 : Int) := fun h => h34 (Int.ofNat.inj h)
  let sE : State := elseBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int)
      (w + 1) s0
  have hSetup : RunsTo
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0) sE := by
    have hs : RunsTo (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int), s0)
        (elseBodyState (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) (w + 1) s0) :=
      runsTo_setup_succ w (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s0 hptr hv
        ⟨it1, it2, it3, it4, i12, i13, i14, i23, i24, i34⟩
    simpa only [sE] using hs
  have hsEptr : sE.ptr = (test : Int) := by simp only [sE, elseBodyState]
  have hsEzero : sE.tape (s3 : Int) = 0 := by
    simp only [sE, elseBodyState]
    rw [if_neg (Ne.symm it3), if_neg (Ne.symm i13), if_neg (Ne.symm i23), if_true]
  have hsEone : sE.tape (s2 : Int) = w + 1 := by
    simp only [sE, elseBodyState]
    rw [if_neg (Ne.symm it2), if_neg (Ne.symm i12), if_true]
  have hElse : RunsTo (bodyLoop (test : Int) (s2 : Int) elseBody, sE)
      { s_else with
        ptr := (test : Int), tape := fun i => if i = (s2 : Int) then 0 else s_else.tape i } :=
    runsTo_bodyLoop_succ w (test : Int) (s2 : Int) elseBody sE s_else hsEptr hsEone helse h1
  have hprog : Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody =
      (ifZeroElseSetup (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) ++
        bodyLoop (test : Int) (s2 : Int) elseBody ++ bodyLoop (test : Int) (s3 : Int) thenBody) :=
    ifZeroElse_eq_chain test s1 s2 s3 s4 thenBody elseBody
  have hElse' : RunsTo (bodyLoop (test : Int) (s2 : Int) elseBody, sE)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
    rw [elsePost_eq test s1 s2 s3 s4 s_else h2 h3 h4 i12 i13 i14 i23 i24 i34] at hElse
    exact hElse
  have hsPostptr :
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else).ptr
      = (test : Int) := by
    simp only [ifZeroElsePost]
  have hsPostzero :
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int)
        s_else).tape (s3 : Int)
      = 0 := by
    simp only [ifZeroElsePost]
    rw [if_neg (Ne.symm i13), if_neg (Ne.symm i23), if_true]
  have hSkip' : RunsTo (bodyLoop (test : Int) (s3 : Int) thenBody,
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else))
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) :=
    runsTo_bodyLoop_zero (test : Int) (s3 : Int) thenBody
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
      hsPostptr hsPostzero
  have hchain :=
    (RunsTo_append (bodyLoop (test : Int) (s3 : Int) thenBody)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
      (RunsTo_append (bodyLoop (test : Int) (s2 : Int) elseBody) sE
        (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
        hSetup hElse')
      hSkip')
  exact RunsTo_eq_program hchain hprog.symm

/-- A zero tested cell runs `thenBody` exactly once (run form). -/
theorem run_ifZeroElse_zero (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_then : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    ∃ fuel, RunsExactly fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
  exact run_of_RunsTo
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then)
    (runsTo_ifZeroElse_zero test s1 s2 s3 s4 thenBody elseBody s0 s_then hptr hv hsep hthen
      h1 h2 h3 h4)

/-- A non-zero tested cell runs `elseBody` exactly once (run form). -/
theorem run_ifZeroElse_succ (w : Nat) (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_else : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = w + 1)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (helse : RunsTo (elseBody, elseBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) (w + 1) s0) s_else)
    (h1 : s_else.ptr = (test : Int)) (h2 : s_else.tape s1 = 0)
    (h3 : s_else.tape s3 = 0) (h4 : s_else.tape s4 = 0) :
    ∃ fuel, RunsExactly fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0
      (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
  exact run_of_RunsTo
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody, s0)
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
    (runsTo_ifZeroElse_succ w test s1 s2 s3 s4 thenBody elseBody s0 s_else hptr hv hsep helse
      h1 h2 h3 h4)

/-- A zero tested cell runs `thenBody` exactly once (fuel-capped form). -/
theorem runToCompletion_ifZeroElse_zero (test s1 s2 s3 s4 : ℕ) (thenBody elseBody : Program)
    (s0 s_then : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = 0)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (hthen : RunsTo (thenBody, thenBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) s0) s_then)
    (h1 : s_then.ptr = (test : Int)) (h2 : s_then.tape s1 = 0)
    (h3 : s_then.tape s2 = 0) (h4 : s_then.tape s4 = 0) :
    ∃ fuel, runToCompletion fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0 =
      some (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then) := by
  rcases run_ifZeroElse_zero test s1 s2 s3 s4 thenBody elseBody s0 s_then hptr hv hsep hthen
      h1 h2 h3 h4 with
    ⟨fuel, hrun, hfull⟩
  exact ⟨fuel + 1, runToCompletion_of_RunsExactly
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) fuel s0
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_then)
    ⟨hrun, hfull⟩⟩

/-- A non-zero tested cell runs `elseBody` exactly once (fuel-capped form). -/
theorem runToCompletion_ifZeroElse_succ (w : Nat) (test s1 s2 s3 s4 : ℕ)
    (thenBody elseBody : Program)
    (s0 s_else : State) (hptr : s0.ptr = (test : Int)) (hv : s0.tape test = w + 1)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s3 ∧ test ≠ s4 ∧
      s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s3 ≠ s4)
    (helse : RunsTo (elseBody, elseBodyState (test : Int) (s1 : Int) (s2 : Int)
      (s3 : Int) (s4 : Int) (w + 1) s0) s_else)
    (h1 : s_else.ptr = (test : Int)) (h2 : s_else.tape s1 = 0)
    (h3 : s_else.tape s3 = 0) (h4 : s_else.tape s4 = 0) :
    ∃ fuel, runToCompletion fuel (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) s0 =
      some (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else) := by
  rcases run_ifZeroElse_succ w test s1 s2 s3 s4 thenBody elseBody s0 s_else hptr hv hsep helse
      h1 h2 h3 h4 with
    ⟨fuel, hrun, hfull⟩
  exact ⟨fuel + 1, runToCompletion_of_RunsExactly
    (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody) fuel s0
    (ifZeroElsePost (test : Int) (s1 : Int) (s2 : Int) (s3 : Int) (s4 : Int) s_else)
    ⟨hrun, hfull⟩⟩

end LeanBF
