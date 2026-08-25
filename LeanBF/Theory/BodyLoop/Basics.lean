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
# Body Loop Basics

The `RunsExactly` exact-run relation and the `bodyLoop` then/else loop: a
zero tested cell skips the body, a non-zero one runs it exactly once, in
`RunsTo` and `run` form.

## Main definitions

* `RunsExactly`: A run that halts after exactly `n` steps.
* `bodyLoop`: The `[movePtr s test ++ body ++ movePtr test s ++ clearHere]`
  body loop.

## Theorems

* `run_of_RunsTo`: A `RunsTo` chain witnesses an exact run.
* `runsExactly_step`: Peeling one step off an exact run shortens it by one.
* `runsExactly_append_suffix`: The suffix phase of an append run is no
  longer than the whole.
* `runsTo_of_loopFree`: A loop-free program runs to `runSeq` completion.
* `runsTo_clearHere`: The clear loop `[-]` clears the current cell.
* `runsTo_bodyLoop_zero`: A zero tested cell skips the body loop.
* `runsTo_bodyLoop_succ`: A non-zero tested cell runs the body exactly once.
* `run_bodyLoop_zero`: The body loop with a zero tested cell (run form).
* `run_bodyLoop_succ`: The body loop with a non-zero tested cell (run form).
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

/-- Peeling one step off an exact run shortens it by exactly one. -/
theorem runsExactly_step (n : Nat) (prog : Program) (s t : State)
    (h : RunsExactly n prog s t) (prog' : Program) (s' : State)
    (hstep : step prog s = some (prog', s')) :
    ∃ m, RunsExactly m prog' s' t ∧ m + 1 = n := by
  cases n with
  | zero =>
      exfalso
      have := h.2
      simp only [stepsToHalt, hstep] at this
      exact Nat.succ_ne_zero 0 this
  | succ k =>
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · have := h.1
        simpa only [run, hstep] using this
      · have := h.2
        simp only [stepsToHalt, hstep, Nat.add_right_cancel_iff] at this
        exact this

/-- If the prefix `B` runs to `s1` and the whole run of `B ++ C` is exact of
    length `n`, then the `C` phase is exact of some length at most `n`. -/
theorem runsExactly_append_suffix (cfg : Program × State) (s1 : State)
    (hB : RunsTo cfg s1) : ∀ (C : Program) (n : Nat) (t : State),
    RunsExactly n (cfg.1 ++ C) cfg.2 t → ∃ m, RunsExactly m C s1 t ∧ m ≤ n := by
  induction hB with
  | halt s0 => intro C n t h; exact ⟨n, by simpa only [List.nil_append] using h, Nat.le_refl n⟩
  | step p s0 s2 p' s_fin hstep hrest ih =>
      intro C n t h
      have happ : step (p ++ C) s0 = some (p' ++ C, s2) := step_append p C s0 s2 p' hstep
      rcases runsExactly_step n (p ++ C) s0 t h (p' ++ C) s2 happ with ⟨k, hk, hkn⟩
      rcases ih C k t hk with ⟨m, hm, hmk⟩
      exact ⟨m, hm, by omega⟩

-- Strict version: a first step costs one, so the suffix is strictly shorter.

end LeanBF
