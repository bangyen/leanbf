/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Compiler
import LeanBF.Core.Semantics
import LeanBF.Theory.Loop
import LeanBF.Theory.Semantics
import LeanBF.Theory.Simulation

/-!
# The `ifZeroElse` Body Loop

The then/else branches of `Compiler.ifZeroElse` are loops that run an arbitrary
body program exactly once when a tested cell is non-zero and not at all when it
is zero. This module pins down that loop in `run`, `RunsTo`, and
`runToCompletion` form, together with the run-composition machinery
(`RunsExactly`, `runToCompletion_append`) that the dispatch simulation uses to
chain loop effects.

## Main definitions

* `RunsExactly`: A run that halts after exactly `n` steps.
* `bodyLoop`: The `[movePtr s test ++ body ++ movePtr test s ++ clearHere]`
  body loop.

## Theorems

* `run_of_RunsTo`: A `RunsTo` chain witnesses an exact run.
* `runsTo_of_loopFree`: A loop-free program runs to `runSeq` completion.
* `runsTo_clearHere`: The clear loop `[-]` clears the current cell.
* `runsTo_bodyLoop_zero`: A zero tested cell skips the body loop.
* `runsTo_bodyLoop_succ`: A non-zero tested cell runs the body exactly once.
* `run_bodyLoop_zero`: The body loop with a zero tested cell (run form).
* `run_bodyLoop_succ`: The body loop with a non-zero tested cell (run form).
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

/-- `RunsExactly n body s s'`: running `body` from `s` halts at `s'` after
    exactly `n` steps. -/
def RunsExactly (n : Nat) (body : Program) (s s' : State) : Prop :=
  run n body s = some s' ∧ stepsToHalt (n + 1) body s = n

/-- A `RunsTo` chain witnesses an exact run. -/
theorem run_of_RunsTo (cfg : Program × State) (s' : State) (h : RunsTo cfg s') :
    ∃ n, RunsExactly n cfg.1 cfg.2 s' := by
  induction h with
  | halt s =>
      refine ⟨0, ?_, ?_⟩
      · rfl
      · rfl
  | step p s s1 p' s_final hstep hrest ih =>
      rcases ih with ⟨n, hrun, hfull⟩
      dsimp only at hrun hfull
      refine ⟨n + 1, ?_, ?_⟩
      · simpa only [run, hstep] using hrun
      · rw [show stepsToHalt ((n + 1) + 1) (p, s).1 (p, s).2 = stepsToHalt (n + 1) p' s1 + 1 by
            simp only [stepsToHalt, hstep]]
        rw [hfull]

/-- A loop-free program runs to `runSeq` completion. -/
theorem runsTo_of_loopFree : ∀ (A : Program) (s : State), LoopFree A →
    RunsTo (A, s) (runSeq A s) := by
  intro A
  induction A with
  | nil => intro s h; exact RunsTo.halt s
  | cons i rest ih =>
      intro s h
      have hstep : step (i :: rest) s = some (rest, stepOne i s) :=
        step_cons_stepOne i rest s h.1
      have hrest : RunsTo (rest, stepOne i s) (runSeq (i :: rest) s) :=
        ih (stepOne i s) h.2
      exact RunsTo.step (i :: rest) s (stepOne i s) rest (runSeq (i :: rest) s) hstep hrest

/-- The clear loop `[-]` clears the current cell to `0`. -/
theorem runsTo_clearHere (v : Nat) (s : State) (hv : s.tape s.ptr = v) :
    RunsTo (Compiler.clearHere, s)
      { s with tape := fun i => if i = s.ptr then 0 else s.tape i } := by
  induction v generalizing s with
  | zero =>
      have hzero : s.currentVal = 0 := by simp only [State.currentVal, hv]
      have hstep : step Compiler.clearHere s = some ([], s) := by
        simp only [Compiler.clearHere, step, if_pos hzero]
      have heq : { s with tape := fun i => if i = s.ptr then 0 else s.tape i } = s := by
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = s.ptr
          · simp only [hi, if_true, hv]
          · simp only [hi, if_false]
        · rfl
        · rfl
      rw [heq]
      exact RunsTo.step Compiler.clearHere s s [] s hstep (RunsTo.halt s)
  | succ v ih =>
      have hne : s.currentVal ≠ 0 := by
        simp only [State.currentVal, hv]
        exact Nat.succ_ne_zero v
      have hstep : step Compiler.clearHere s = some ([.dec_val] ++ Compiler.clearHere, s) := by
        simp only [Compiler.clearHere, step, if_neg hne, List.append_nil]
      have hdec : RunsTo ([.dec_val], s) s.decVal := by
        have hstep' : step [.dec_val] s = some ([], s.decVal) := by
          simp only [step]
        exact RunsTo.step [.dec_val] s s.decVal [] s.decVal hstep' (RunsTo.halt s.decVal)
      have hdecTape : (s.decVal).tape (s.decVal).ptr = v := by
        simp only [State.decVal, State.modifyCell, hv, Nat.add_sub_cancel, if_true]
      have hrest : RunsTo (Compiler.clearHere, s.decVal)
          { s.decVal with tape := fun i => if i = (s.decVal).ptr then 0 else (s.decVal).tape i } :=
        ih (s.decVal) hdecTape
      have hchain : RunsTo ([.dec_val] ++ Compiler.clearHere, s)
          { s.decVal with tape := fun i => if i = (s.decVal).ptr then 0 else (s.decVal).tape i } :=
        RunsTo_append Compiler.clearHere s.decVal
          { s.decVal with tape := fun i => if i = (s.decVal).ptr then 0 else (s.decVal).tape i }
          hdec hrest
      have hfinal :
          { s.decVal with tape := fun i => if i = (s.decVal).ptr then 0 else (s.decVal).tape i }
          = { s with tape := fun i => if i = s.ptr then 0 else s.tape i } := by
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = s.ptr
          · simp only [hi, if_true, State.decVal, State.modifyCell]
          · simp only [hi, if_false, State.decVal, State.modifyCell]
        · rfl
        · rfl
      rw [hfinal] at hchain
      exact RunsTo.step Compiler.clearHere s s ([.dec_val] ++ Compiler.clearHere)
        { s with tape := fun i => if i = s.ptr then 0 else s.tape i } hstep hchain

/-- The body loop used by `Compiler.ifZeroElse`: move to the tested cell `s`,
    run `body` exactly once when `s` is non-zero (skipping it when `s` is
    zero), then clear `s` and return to `test`. -/
def bodyLoop (test s : Int) (body : Program) : Program :=
  Compiler.movePtr test s ++
    ([.loop (Compiler.movePtr s test ++
      (body ++ (Compiler.movePtr test s ++ Compiler.clearHere)))] ++
      Compiler.movePtr s test)

/-- A zero tested cell skips the body loop: the state is unchanged and the
    pointer returns to `test`. -/
theorem runsTo_bodyLoop_zero (test s : Int) (body : Program) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = 0) :
    RunsTo (bodyLoop test s body, s0) s0 := by
  let MA : Program := Compiler.movePtr test s
  let MB : Program := Compiler.movePtr s test
  let L : Program := MB ++ (body ++ (MA ++ Compiler.clearHere))
  change RunsTo (MA ++ ([.loop L] ++ MB), s0) s0
  have hMA : RunsTo (MA, s0) (runSeq MA s0) := runsTo_of_loopFree MA s0 (loop_free_movePtr test s)
  have hMAptr : (runSeq MA s0).ptr = s := runSeq_movePtr_ptr test s s0 hptr
  have hMAtape : (runSeq MA s0).tape = s0.tape := runSeq_movePtr_tape test s s0
  let sA : State := runSeq MA s0
  have hsAtape : sA.tape s = 0 := by
    simp only [sA, hMAtape, hv]
  have hskip : RunsTo ([.loop L], sA) sA := by
    have hcur : sA.currentVal = 0 := by
      simp only [sA, State.currentVal, hMAptr, hsAtape]
    have hstep : step [.loop L] sA = some ([], sA) := step_loop_zero sA L hcur
    exact RunsTo.step [.loop L] sA sA [] sA hstep (RunsTo.halt sA)
  have hMB : RunsTo (MB, sA) s0 := by
    have hMB' : RunsTo (MB, sA) (runSeq MB sA) :=
      runsTo_of_loopFree MB sA (loop_free_movePtr s test)
    have hsc : runSeq MB sA = s0 := by
      apply State.ext
      · rw [runSeq_movePtr_ptr s test sA hMAptr, hptr]
      · rw [runSeq_movePtr_tape s test sA, hMAtape]
      · rw [(runSeq_movePtr_io s test sA).1, (runSeq_movePtr_io test s s0).1]
      · rw [(runSeq_movePtr_io s test sA).2, (runSeq_movePtr_io test s s0).2]
    rw [hsc] at hMB'
    exact hMB'
  exact RunsTo_append ([.loop L] ++ MB) sA s0 hMA (RunsTo_append MB sA s0 hskip hMB)

/-- A non-zero tested cell runs the body exactly once: from a state with `s`
    holding `w + 1`, running the loop reaches the state reached by the body
    with the pointer back on `test` and `s` cleared. -/
theorem runsTo_bodyLoop_succ (w : Nat) (test s : Int) (body : Program) (s0 s1 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = w + 1)
    (hbody : RunsTo (body, { s0 with ptr := test }) s1) (h1ptr : s1.ptr = test) :
    RunsTo (bodyLoop test s body, s0)
      { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } := by
  let MA : Program := Compiler.movePtr test s
  let MB : Program := Compiler.movePtr s test
  let L : Program := MB ++ (body ++ (MA ++ Compiler.clearHere))
  change RunsTo (MA ++ ([.loop L] ++ MB), s0)
      { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i }
  have hMA : RunsTo (MA, s0) (runSeq MA s0) := runsTo_of_loopFree MA s0 (loop_free_movePtr test s)
  have hMAptr : (runSeq MA s0).ptr = s := runSeq_movePtr_ptr test s s0 hptr
  have hMAtape : (runSeq MA s0).tape = s0.tape := runSeq_movePtr_tape test s s0
  let sA : State := runSeq MA s0
  have hsAcur : sA.currentVal = w + 1 := by
    simp only [sA, State.currentVal, hMAptr, hMAtape, hv]
  have hne : sA.currentVal ≠ 0 := by
    intro h
    rw [hsAcur] at h
    exact Nat.succ_ne_zero w h
  have hstep : step [.loop L] sA = some (L ++ [.loop L], sA) := step_loop_nonzero sA L hne
  have hMB1 : RunsTo (MB, sA) (runSeq MB sA) := runsTo_of_loopFree MB sA (loop_free_movePtr s test)
  have hMB1ptr : (runSeq MB sA).ptr = test := runSeq_movePtr_ptr s test sA hMAptr
  let sB : State := runSeq MB sA
  have hsB : sB = { s0 with ptr := test } := by
    apply State.ext
    · simpa only [hMB1ptr]
    · rw [runSeq_movePtr_tape s test sA, hMAtape]
    · rw [(runSeq_movePtr_io s test sA).1, (runSeq_movePtr_io test s s0).1]
    · rw [(runSeq_movePtr_io s test sA).2, (runSeq_movePtr_io test s s0).2]
  have hbody' : RunsTo (body, sB) s1 := by
    rw [hsB]
    exact hbody
  have hMA2 : RunsTo (MA, s1) (runSeq MA s1) := runsTo_of_loopFree MA s1 (loop_free_movePtr test s)
  have hMA2ptr : (runSeq MA s1).ptr = s := runSeq_movePtr_ptr test s s1 h1ptr
  let sM : State := runSeq MA s1
  let sC : State := { sM with tape := fun i => if i = s then 0 else sM.tape i }
  have hC : RunsTo (Compiler.clearHere, sM) sC := by
    have hC0 : RunsTo (Compiler.clearHere, sM)
        { sM with tape := fun i => if i = sM.ptr then 0 else sM.tape i } :=
      runsTo_clearHere (sM.tape sM.ptr) sM rfl
    have heq : { sM with tape := fun i => if i = sM.ptr then 0 else sM.tape i } = sC := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = s
        · simp only [hi, sC, sM, MA, if_true, runSeq_movePtr_ptr test s s1 h1ptr]
        · simp only [hi, sC, sM, MA, if_false, runSeq_movePtr_ptr test s s1 h1ptr]
      · rfl
      · rfl
    rw [heq] at hC0
    exact hC0
  have hL : RunsTo (L, sA) sC := by
    dsimp only [L]
    have hMAclear : RunsTo (MA ++ Compiler.clearHere, s1) sC := by
      exact RunsTo_append Compiler.clearHere sM sC hMA2 hC
    have hbodyrest : RunsTo (body ++ (MA ++ Compiler.clearHere), sB) sC := by
      exact RunsTo_append (MA ++ Compiler.clearHere) s1 sC hbody' hMAclear
    exact RunsTo_append (body ++ (MA ++ Compiler.clearHere)) sB sC hMB1 hbodyrest
  have hsCptr : sC.ptr = s := by
    simp only [sC, sM, MA, runSeq_movePtr_ptr test s s1 h1ptr]
  have hsCtape : sC.tape s = 0 := by
    simp only [sC, if_true]
  have hskip : RunsTo ([.loop L], sC) sC := by
    have hcur : sC.currentVal = 0 := by
      simp only [sC, sM, MA, State.currentVal, runSeq_movePtr_ptr test s s1 h1ptr, if_true]
    have hstep' : step [.loop L] sC = some ([], sC) := step_loop_zero sC L hcur
    exact RunsTo.step [.loop L] sC sC [] sC hstep' (RunsTo.halt sC)
  have hloop : RunsTo ([.loop L], sA) sC := by
    have hchain : RunsTo (L ++ [.loop L], sA) sC := RunsTo_append [.loop L] sC sC hL hskip
    exact RunsTo.step [.loop L] sA sA (L ++ [.loop L]) sC hstep hchain
  have hMB2 : RunsTo (MB, sC)
      { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } := by
    have hMB2' : RunsTo (MB, sC) (runSeq MB sC) :=
      runsTo_of_loopFree MB sC (loop_free_movePtr s test)
    have hsc : runSeq MB sC =
        { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } := by
      apply State.ext
      · simp only [MB, runSeq_movePtr_ptr s test sC hsCptr]
      · funext i
        rw [runSeq_movePtr_tape s test sC]
        change sC.tape i = (if i = s then 0 else s1.tape i)
        by_cases hi : i = s
        · simp only [hi, sC, if_true]
        · simp only [hi, sC, if_false, sM, MA, runSeq_movePtr_tape test s s1]
      · rw [(runSeq_movePtr_io s test sC).1]
        change sC.input = s1.input
        simp only [sC, sM, MA, (runSeq_movePtr_io test s s1).1]
      · rw [(runSeq_movePtr_io s test sC).2]
        change sC.output = s1.output
        simp only [sC, sM, MA, (runSeq_movePtr_io test s s1).2]
    rw [hsc] at hMB2'
    exact hMB2'
  exact RunsTo_append ([.loop L] ++ MB) sA
    { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i }
    hMA (RunsTo_append MB sC
      { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i }
      hloop hMB2)

/-- The body loop with a zero tested cell (run form). -/
theorem run_bodyLoop_zero (test s : Int) (body : Program) (s0 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = 0) :
    ∃ fuel, RunsExactly fuel (bodyLoop test s body) s0 s0 := by
  exact run_of_RunsTo (bodyLoop test s body, s0) s0 (runsTo_bodyLoop_zero test s body s0 hptr hv)

/-- The body loop with a non-zero tested cell (run form). -/
theorem run_bodyLoop_succ (w : Nat) (test s : Int) (body : Program) (s0 s1 : State)
    (hptr : s0.ptr = test) (hv : s0.tape s = w + 1)
    (hbody : RunsTo (body, { s0 with ptr := test }) s1) (h1ptr : s1.ptr = test) :
    ∃ fuel, RunsExactly fuel (bodyLoop test s body) s0
      { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i } := by
  exact run_of_RunsTo (bodyLoop test s body, s0)
    { s1 with ptr := test, tape := fun i => if i = s then 0 else s1.tape i }
    (runsTo_bodyLoop_succ w test s body s0 s1 hptr hv hbody h1ptr)

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
