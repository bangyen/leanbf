/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Compiler
import LeanBF.Core.Semantics
import LeanBF.Theory.BodyLoop.Basics
import LeanBF.Theory.Loop
import LeanBF.Theory.Semantics
import LeanBF.Theory.Simulation

/-!
# Body Loop Completion

Fuel-capped forms of the `bodyLoop`: completed runs convert back into
`RunsTo` chains, exact runs complete with one unit of spare fuel, completed
runs compose across concatenation, and the body loop is shown to complete.

## Theorems

* `runsTo_of_runToCompletion_eq`: A completed fuel-capped run gives a `RunsTo`
  chain with the same final state.
* `runToCompletion_of_RunsExactly`: An exact run completes with one unit of
  spare fuel.
* `runToCompletion_append`: Completed runs compose across concatenation.
* `runToCompletion_bodyLoop_zero`: The body loop with a zero tested cell
  (fuel-capped form).
* `runToCompletion_bodyLoop_succ`: The body loop with a non-zero tested cell
  (fuel-capped form).
-/

namespace LeanBF

/-- A completed fuel-capped run gives a `RunsTo` chain with the same final
    state. -/
theorem runsTo_of_runToCompletion_eq (fuel : Nat) (prog : Program) (s s' : State)
    (h : runToCompletion fuel prog s = some s') : RunsTo (prog, s) s' := by
  induction fuel generalizing prog s with
  | zero =>
      have hnone : runToCompletion 0 prog s = none := by simp only [runToCompletion]
      rw [hnone] at h
      cases h
  | succ fuel ih =>
      cases hstep : step prog s with
      | none =>
          have hprog : prog = [] := (step_none_iff_empty prog s).mp hstep
          subst prog
          have hs' : s' = s := by
            simp only [runToCompletion, hstep] at h
            exact Option.some.inj h.symm
          subst s'
          exact RunsTo.halt s
      | some cfg =>
          rcases cfg with ⟨prog', s1⟩
          have h' : runToCompletion fuel prog' s1 = some s' := by
            simpa only [runToCompletion, hstep] using h
          have ih' : RunsTo (prog', s1) s' := ih prog' s1 h'
          exact RunsTo.step prog s s1 prog' s' hstep ih'

/-- An exact run completes with one unit of spare fuel. -/
theorem runToCompletion_of_RunsExactly (prog : Program) (n : Nat) (s s' : State)
    (h : RunsExactly n prog s s') : runToCompletion (n + 1) prog s = some s' := by
  rcases h with ⟨hrun, hfull⟩
  induction n generalizing prog s with
  | zero =>
      have hnil : prog = [] := (stepsToHalt_one_eq_zero prog s).mp hfull
      subst prog
      have hs' : s' = s := by
        simp only [run] at hrun
        exact Option.some.inj hrun.symm
      subst s'
      rw [show (0 + 1) = 1 by rfl]
      rfl
  | succ m ih =>
      have hne : prog ≠ [] := by
        intro hnil
        subst prog
        have h0 : stepsToHalt (m + 2) [] s = 0 := by simp only [stepsToHalt, step_empty]
        have hm : stepsToHalt (m + 2) [] s = m + 1 := by
          simpa only using hfull
        exact Nat.succ_ne_zero m (hm.symm.trans h0)
      cases hstep : step prog s with
      | some cfg =>
          rcases cfg with ⟨prog', s1⟩
          have hcalc : stepsToHalt ((m + 1) + 1) prog s = stepsToHalt (m + 1) prog' s1 + 1 := by
            simp only [stepsToHalt, hstep]
          have hfull' : stepsToHalt (m + 1) prog' s1 = m := by
            exact Nat.succ.inj (hcalc.symm.trans hfull)
          have hrun' : run m prog' s1 = some s' := by
            simpa only [run, hstep] using hrun
          have ih' := ih prog' s1 hrun' hfull'
          simpa only [runToCompletion, hstep] using ih'
      | none =>
          exact False.elim (hne ((step_none_iff_empty prog s).mp hstep))

/-- Completed runs compose across concatenation: if `A` completes from `s` at
    `s'` and `B` completes from `s'` at `s''`, then `A ++ B` completes from
    `s` at `s''`. -/
theorem runToCompletion_append (n k : Nat) (A B : Program) (s s' s'' : State)
    (hA : runToCompletion n A s = some s')
    (hB : runToCompletion k B s' = some s'') :
    runToCompletion (n + k) (A ++ B) s = some s'' := by
  induction n generalizing A s with
  | zero =>
      have hnone : runToCompletion 0 A s = none := by simp only [runToCompletion]
      rw [hnone] at hA
      cases hA
  | succ m ih =>
      cases hstep : step A s with
      | none =>
          have hAempty : A = [] := (step_none_iff_empty A s).mp hstep
          subst A
          have hs' : s' = s := by
            simp only [runToCompletion, hstep] at hA
            exact Option.some.inj hA.symm
          subst s'
          have hBne : runToCompletion k B s ≠ none := by
            intro h
            rw [hB] at h
            cases h
          have hge := runToCompletion_eq_of_ge k (m + 1) B s hBne
          rw [show (m + 1) + k = k + (m + 1) by rw [Nat.add_comm]]
          rw [show ([] : Program) ++ B = B by rfl]
          rw [hge]
          exact hB
      | some cfg =>
          rcases cfg with ⟨A', s1⟩
          have hA' : runToCompletion m A' s1 = some s' := by
            simpa only [runToCompletion, hstep] using hA
          have hstepApp := step_append A B s s1 A' hstep
          have ih' := ih A' s1 hA'
          rw [show (m + 1) + k = Nat.succ (m + k) by rw [Nat.succ_eq_add_one]; ring]
          simp only [runToCompletion, hstepApp]
          exact ih'

/-- The body loop with a zero tested cell (fuel-capped form). -/
theorem runToCompletion_bodyLoop_zero (test s : Int) (body : Program) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = 0) :
    ∃ fuel, runToCompletion fuel (bodyLoop test s body) s0 = some s0 := by
  rcases run_bodyLoop_zero test s body s0 hptr hv with ⟨fuel, hrun, hfull⟩
  exact ⟨fuel + 1, runToCompletion_of_RunsExactly (bodyLoop test s body) fuel s0 s0
    ⟨hrun, hfull⟩⟩

/-- The body loop with a non-zero tested cell (fuel-capped form). -/
theorem runToCompletion_bodyLoop_succ (w : Nat) (test s : Int) (body : Program) (s0 s1 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = w + 1)
    (hbody : ∃ fuel, runToCompletion fuel body { s0 with ptr := test } = some s1)
    (h1ptr : s1.ptr = test) :
    ∃ fuel, runToCompletion fuel (bodyLoop test s body) s0 =
      some { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } := by
  rcases hbody with ⟨fuel, hbody'⟩
  have hrunsTo : RunsTo (body, { s0 with ptr := test }) s1 :=
    runsTo_of_runToCompletion_eq fuel body { s0 with ptr := test } s1 hbody'
  rcases run_bodyLoop_succ w test s body s0 s1 hptr hv hrunsTo h1ptr with
    ⟨fuel', hrun, hfull⟩
  exact ⟨fuel' + 1, runToCompletion_of_RunsExactly (bodyLoop test s body) fuel' s0
    { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } ⟨hrun, hfull⟩⟩

end LeanBF
