/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.Dispatch

/-!
# Compile Program and Completeness

The compiled program's loop body, the compiled program running a Minsky
machine to completion, and the `turingCompleteness` proof.

## Theorems

* `runsTo_compileBody`: The loop body maps a simulating state to the
  dispatched machine state.
* `runsTo_compileProgram`: The compiled program runs the Minsky machine and
  clears the running flag.
* `terminal_of_RunsTo`: The final state of a Minsky run is terminal.
* `turingCompleteness_proof`: The proof of `turingCompleteness`.
-/

namespace LeanBF

/-- One iteration of the `compileProgram` loop: clear `done`, dispatch, and
    clear the running flag if no window matched. -/
theorem runsTo_compileBody (m : Minsky.Program) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 0 s) (hrun : s.tape 0 = 1)
    (hclean : s.tape 5 = 0 ∧ s.tape 6 = 0 ∧ s.tape 7 = 0 ∧ s.tape 8 = 0) :
    ∃ s', RunsTo (Compiler.movePtr 0 4 ++ Compiler.clearHere ++
        List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr)) ++
        Compiler.ifZeroElse 4 5 6 7 8
          (Compiler.movePtr 4 0 ++ Compiler.clearHere ++ Compiler.movePtr 0 4) [] ++
        Compiler.movePtr 4 0, s) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = (if dispatchDone m ms then dispatchRunning m ms else 0) ∧
        s'.tape 1 = (dispatchMs m ms).pc ∧ s'.tape 2 = (dispatchMs m ms).c1 ∧
        s'.tape 3 = (dispatchMs m ms).c2 ∧
        s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧ s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  rcases hsim with ⟨hsptr, hspc, hsc1, hsc2, hsrunning⟩
  rcases hclean with ⟨h5, h6, h7, h8⟩
  let a1 : State := { s with ptr := 4 }
  have h1 : RunsTo (Compiler.movePtr 0 4, s) a1 := by
    simpa only [a1] using runsTo_movePtr 0 4 s hsptr
  have ha1ptr : a1.ptr = 4 := by simp only [a1]
  have ha1pc : a1.tape 1 = ms.pc := by simp only [a1, hspc]
  have ha1c1 : a1.tape 2 = ms.c1 := by simp only [a1, hsc1]
  have ha1c2 : a1.tape 3 = ms.c2 := by simp only [a1, hsc2]
  have ha1run : a1.tape 0 = 1 := by simp only [a1, hrun]
  have ha1clean : a1.tape 5 = 0 ∧ a1.tape 6 = 0 ∧ a1.tape 7 = 0 ∧ a1.tape 8 = 0 := by
    exact ⟨by simp only [a1, h5], by simp only [a1, h6], by simp only [a1, h7],
      by simp only [a1, h8]⟩
  let a2 : State := { a1 with tape := fun i => if i = (4 : Int) then 0 else a1.tape i }
  have h2 : RunsTo (Compiler.clearHere, a1) a2 := by
    have hc : RunsTo (Compiler.clearHere, a1)
        { a1 with tape := fun i => if i = a1.ptr then 0 else a1.tape i } :=
      runsTo_clearHere (a1.tape a1.ptr) a1 rfl
    have heq : { a1 with tape := fun i => if i = a1.ptr then 0 else a1.tape i } = a2 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (4 : Int)
        · simp only [hi, if_true, a2, a1]
        · simp only [if_neg hi, a2, a1]
      · rfl
      · rfl
    rw [heq] at hc
    exact hc
  have ha2sim : SimulatesAt ms 4 a2 := by
    simp only [SimulatesAt, a2, a1]
    constructor
    · trivial
    · constructor
      · rw [if_neg (by decide : ¬ (1 : Int) = 4)]
        exact hspc
      · constructor
        · rw [if_neg (by decide : ¬ (2 : Int) = 4)]
          exact hsc1
        · constructor
          · rw [if_neg (by decide : ¬ (3 : Int) = 4)]
            exact hsc2
          · rw [if_neg (by decide : ¬ (0 : Int) = 4)]
            exact hsrunning
  have ha2done : a2.tape 4 = 0 := by
    simp only [a2, a1]
    rw [if_true]
  have ha2clean : a2.tape 5 = 0 ∧ a2.tape 6 = 0 ∧ a2.tape 7 = 0 ∧ a2.tape 8 = 0 := by
    simp only [a2, a1]
    constructor
    · rw [if_neg (by decide : ¬ (5 : Int) = 4)]
      exact h5
    · constructor
      · rw [if_neg (by decide : ¬ (6 : Int) = 4)]
        exact h6
      · constructor
        · rw [if_neg (by decide : ¬ (7 : Int) = 4)]
          exact h7
        · rw [if_neg (by decide : ¬ (8 : Int) = 4)]
          exact h8
  rcases runsTo_dispatch m ms a2 ha2sim ha2done ha2clean with
    ⟨a3, h3, h3ptr, h3done, h3run, h3pc, h3c1, h3c2, h35, h36, h37, h38⟩
  let tb : Program := Compiler.movePtr 4 0 ++ Compiler.clearHere ++ Compiler.movePtr 0 4
  by_cases hD : dispatchDone m ms
  · have hd1 : a3.tape 4 = 1 := by
      simp only [h3done, hD, if_true]
    let s_else : State := elseBodyState 4 5 6 7 8 1 a3
    have helse : RunsTo ([], s_else) s_else := RunsTo.halt s_else
    have h1e : s_else.ptr = 4 := by simp only [s_else, elseBodyState]
    have h2e : s_else.tape 5 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (5 : Int) = 4), if_true]
    have h3e : s_else.tape 7 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (7 : Int) = 4), if_neg (by decide : ¬ (7 : Int) = 5),
        if_neg (by decide : ¬ (7 : Int) = 6), if_true]
    have h4e : s_else.tape 8 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (8 : Int) = 4), if_neg (by decide : ¬ (8 : Int) = 5),
        if_neg (by decide : ¬ (8 : Int) = 6), if_neg (by decide : ¬ (8 : Int) = 7), if_true]
    have hif : RunsTo (Compiler.ifZeroElse 4 5 6 7 8 tb [], a3)
        (ifZeroElsePost 4 5 6 7 8 s_else) :=
      runsTo_ifZeroElse_succ 0 4 5 6 7 8 tb [] a3 s_else h3ptr hd1
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ helse h1e h2e h3e h4e
    let a4 : State := ifZeroElsePost 4 5 6 7 8 s_else
    have ha4run : a4.tape 0 = dispatchRunning m ms := by
      simp only [a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (0 : Int) = 4)]
      rw [if_neg (by decide : ¬ (0 : Int) = 5), if_neg (by decide : ¬ (0 : Int) = 6),
        if_neg (by decide : ¬ (0 : Int) = 7), if_neg (by decide : ¬ (0 : Int) = 8)]
      exact h3run
    let a5 : State := { a4 with ptr := 0 }
    have h5 : RunsTo (Compiler.movePtr 4 0, a4) a5 := by
      have hp : a4.ptr = 4 := by simp only [a4, ifZeroElsePost]
      simpa only [a5] using runsTo_movePtr 4 0 a4 hp
    have hchain : RunsTo (Compiler.movePtr 0 4 ++ Compiler.clearHere ++
        List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr)) ++
        Compiler.ifZeroElse 4 5 6 7 8 tb [] ++ Compiler.movePtr 4 0, s) a5 := by
      simpa only [List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 4 0) a4 a5
          (RunsTo_append (Compiler.ifZeroElse 4 5 6 7 8 tb []) a3 a4
            (RunsTo_append (List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr))) a2 a3
              (RunsTo_append Compiler.clearHere a1 a2 h1 h2) h3)
            hif)
          h5)
    refine ⟨a5, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rw [hD]
      exact ha4run
    · simp only [a5, a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (1 : Int) = 4), if_neg (by decide : ¬ (1 : Int) = 5),
        if_neg (by decide : ¬ (1 : Int) = 6), if_neg (by decide : ¬ (1 : Int) = 7),
        if_neg (by decide : ¬ (1 : Int) = 8)]
      exact h3pc
    · simp only [a5, a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (2 : Int) = 4), if_neg (by decide : ¬ (2 : Int) = 5),
        if_neg (by decide : ¬ (2 : Int) = 6), if_neg (by decide : ¬ (2 : Int) = 7),
        if_neg (by decide : ¬ (2 : Int) = 8)]
      exact h3c1
    · simp only [a5, a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (3 : Int) = 4), if_neg (by decide : ¬ (3 : Int) = 5),
        if_neg (by decide : ¬ (3 : Int) = 6), if_neg (by decide : ¬ (3 : Int) = 7),
        if_neg (by decide : ¬ (3 : Int) = 8)]
      exact h3c2
    · simp only [a5, a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (5 : Int) = 4), if_true]
    · simp only [a5, a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (6 : Int) = 4), if_neg (by decide : ¬ (6 : Int) = 5), if_true]
    · simp only [a5, a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (7 : Int) = 4), if_neg (by decide : ¬ (7 : Int) = 5),
        if_neg (by decide : ¬ (7 : Int) = 6), if_true]
    · simp only [a5, a4, ifZeroElsePost, s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (8 : Int) = 4), if_neg (by decide : ¬ (8 : Int) = 5),
        if_neg (by decide : ¬ (8 : Int) = 6), if_neg (by decide : ¬ (8 : Int) = 7), if_true]
  · have hd0 : a3.tape 4 = 0 := by
      rw [h3done]
      rw [if_neg hD]
    let m1 : State := { thenBodyState 4 5 6 7 8 a3 with ptr := 0 }
    let m2 : State := { m1 with tape := fun i => if i = (0 : Int) then 0 else m1.tape i }
    let m3 : State := { m2 with ptr := 4 }
    have hm1 : RunsTo (Compiler.movePtr 4 0, thenBodyState 4 5 6 7 8 a3) m1 := by
      simpa only [m1] using runsTo_movePtr 4 0 (thenBodyState 4 5 6 7 8 a3)
        (by simp only [thenBodyState])
    have hm2 : RunsTo (Compiler.clearHere, m1) m2 := by
      have hc : RunsTo (Compiler.clearHere, m1)
          { m1 with tape := fun i => if i = m1.ptr then 0 else m1.tape i } :=
        runsTo_clearHere (m1.tape m1.ptr) m1 rfl
      have heq : { m1 with tape := fun i => if i = m1.ptr then 0 else m1.tape i } = m2 := by
        apply State.ext
        · rfl
        · funext i
          by_cases hi : i = (0 : Int)
          · simp only [hi, if_true, m2, m1]
          · simp only [if_neg hi, m2, m1]
        · rfl
        · rfl
      rw [heq] at hc
      exact hc
    have hm2ptr : m2.ptr = 0 := by simp only [m2, m1]
    have hm3 : RunsTo (Compiler.movePtr 0 4, m2) m3 := by
      simpa only [m3] using runsTo_movePtr 0 4 m2 hm2ptr
    have hThen : RunsTo (tb, thenBodyState 4 5 6 7 8 a3) m3 := by
      simpa only [tb, List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 0 4) m2 m3
          (RunsTo_append Compiler.clearHere m1 m2 hm1 hm2) hm3)
    have hsptr : m3.ptr = 4 := by simp only [m3]
    have h2t : m3.tape 5 = 0 := by
      simp only [m3, m2, m1]
      rw [if_neg (by decide : ¬ (5 : Int) = 0)]
      simp only [thenBodyState]
      rw [if_neg (by decide : ¬ (5 : Int) = 4), if_true]
    have h3t : m3.tape 6 = 0 := by
      simp only [m3, m2, m1]
      rw [if_neg (by decide : ¬ (6 : Int) = 0)]
      simp only [thenBodyState]
      rw [if_neg (by decide : ¬ (6 : Int) = 4), if_neg (by decide : ¬ (6 : Int) = 5), if_true]
    have h4t : m3.tape 8 = 0 := by
      simp only [m3, m2, m1]
      rw [if_neg (by decide : ¬ (8 : Int) = 0)]
      simp only [thenBodyState]
      rw [if_neg (by decide : ¬ (8 : Int) = 4), if_neg (by decide : ¬ (8 : Int) = 5),
        if_neg (by decide : ¬ (8 : Int) = 6), if_neg (by decide : ¬ (8 : Int) = 7), if_true]
    have hif : RunsTo (Compiler.ifZeroElse 4 5 6 7 8 tb [], a3)
        (ifZeroElsePost 4 5 6 7 8 m3) :=
      runsTo_ifZeroElse_zero 4 5 6 7 8 tb [] a3 m3 h3ptr hd0
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ hThen hsptr h2t h3t h4t
    let a4 : State := ifZeroElsePost 4 5 6 7 8 m3
    have ha4run : a4.tape 0 = 0 := by
      change (ifZeroElsePost 4 5 6 7 8 m3).tape 0 = 0
      rw [ifZeroElsePost_tape 4 5 6 7 8 m3 (by decide : ¬ (0 : Int) = 5)
        (by decide : ¬ (0 : Int) = 6) (by decide : ¬ (0 : Int) = 7) (by decide : ¬ (0 : Int) = 8)]
      simp only [m3, m2, m1, if_true]
    have hm3cell : ∀ {i : Int}, i ≠ (0 : Int) → i ≠ (4 : Int) → i ≠ (5 : Int) →
        i ≠ (6 : Int) → i ≠ (7 : Int) → i ≠ (8 : Int) → m3.tape i = a3.tape i := by
      intro i h0 h4 h5 h6 h7 h8
      change m3.tape i = a3.tape i
      simp only [m3, m2, m1, if_neg h0]
      rw [thenBodyState_tape 4 5 6 7 8 a3 h4 h5 h6 h7 h8]
    have ha4pc : a4.tape 1 = (dispatchMs m ms).pc := by
      change (ifZeroElsePost 4 5 6 7 8 m3).tape 1 = (dispatchMs m ms).pc
      rw [ifZeroElsePost_tape 4 5 6 7 8 m3 (by decide : ¬ (1 : Int) = 5)
        (by decide : ¬ (1 : Int) = 6) (by decide : ¬ (1 : Int) = 7) (by decide : ¬ (1 : Int) = 8)]
      rw [hm3cell (by decide : ¬ (1 : Int) = 0) (by decide : ¬ (1 : Int) = 4)
        (by decide : ¬ (1 : Int) = 5) (by decide : ¬ (1 : Int) = 6)
        (by decide : ¬ (1 : Int) = 7) (by decide : ¬ (1 : Int) = 8)]
      exact h3pc
    have ha4c1 : a4.tape 2 = (dispatchMs m ms).c1 := by
      change (ifZeroElsePost 4 5 6 7 8 m3).tape 2 = (dispatchMs m ms).c1
      rw [ifZeroElsePost_tape 4 5 6 7 8 m3 (by decide : ¬ (2 : Int) = 5)
        (by decide : ¬ (2 : Int) = 6) (by decide : ¬ (2 : Int) = 7) (by decide : ¬ (2 : Int) = 8)]
      rw [hm3cell (by decide : ¬ (2 : Int) = 0) (by decide : ¬ (2 : Int) = 4)
        (by decide : ¬ (2 : Int) = 5) (by decide : ¬ (2 : Int) = 6)
        (by decide : ¬ (2 : Int) = 7) (by decide : ¬ (2 : Int) = 8)]
      exact h3c1
    have ha4c2 : a4.tape 3 = (dispatchMs m ms).c2 := by
      change (ifZeroElsePost 4 5 6 7 8 m3).tape 3 = (dispatchMs m ms).c2
      rw [ifZeroElsePost_tape 4 5 6 7 8 m3 (by decide : ¬ (3 : Int) = 5)
        (by decide : ¬ (3 : Int) = 6) (by decide : ¬ (3 : Int) = 7) (by decide : ¬ (3 : Int) = 8)]
      rw [hm3cell (by decide : ¬ (3 : Int) = 0) (by decide : ¬ (3 : Int) = 4)
        (by decide : ¬ (3 : Int) = 5) (by decide : ¬ (3 : Int) = 6)
        (by decide : ¬ (3 : Int) = 7) (by decide : ¬ (3 : Int) = 8)]
      exact h3c2
    have ha4tape5 : a4.tape 5 = 0 := by simp only [a4, ifZeroElsePost]; rw [if_true]
    have ha4tape6 : a4.tape 6 = 0 := by
      simp only [a4, ifZeroElsePost]
      rw [if_neg (by decide : ¬ (6 : Int) = 5), if_true]
    have ha4tape7 : a4.tape 7 = 0 := by
      simp only [a4, ifZeroElsePost]
      rw [if_neg (by decide : ¬ (7 : Int) = 5), if_neg (by decide : ¬ (7 : Int) = 6), if_true]
    have ha4tape8 : a4.tape 8 = 0 := by
      simp only [a4, ifZeroElsePost]
      rw [if_neg (by decide : ¬ (8 : Int) = 5), if_neg (by decide : ¬ (8 : Int) = 6),
        if_neg (by decide : ¬ (8 : Int) = 7), if_true]
    let a5 : State := { a4 with ptr := 0 }
    have h5 : RunsTo (Compiler.movePtr 4 0, a4) a5 := by
      have hp : a4.ptr = 4 := by simp only [a4, ifZeroElsePost]
      simpa only [a5] using runsTo_movePtr 4 0 a4 hp
    have hchain : RunsTo (Compiler.movePtr 0 4 ++ Compiler.clearHere ++
        List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr)) ++
        Compiler.ifZeroElse 4 5 6 7 8 tb [] ++ Compiler.movePtr 4 0, s) a5 := by
      simpa only [List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 4 0) a4 a5
          (RunsTo_append (Compiler.ifZeroElse 4 5 6 7 8 tb []) a3 a4
            (RunsTo_append (List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr))) a2 a3
              (RunsTo_append Compiler.clearHere a1 a2 h1 h2) h3)
            hif)
          h5)
    refine ⟨a5, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [hD]
      exact ha4run
    · simp only [a5, ha4pc]
    · simp only [a5, ha4c1]
    · simp only [a5, ha4c2]
    · simp only [a5, ha4tape5]
    · simp only [a5, ha4tape6]
    · simp only [a5, ha4tape7]
    · simp only [a5, ha4tape8]

/-- The compiled program runs a Minsky machine to its terminal state, then
    clears the running flag. -/
theorem runsTo_compileProgram (m : Minsky.Program) (ms ms' : Minsky.State) (s : State)
    (hr : Minsky.RunsTo m ms ms') (hsim : SimulatesAt ms 0 s)
    (hclean : s.tape 5 = 0 ∧ s.tape 6 = 0 ∧ s.tape 7 = 0 ∧ s.tape 8 = 0) :
    ∃ s', RunsTo (Compiler.compileProgram m, s) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧
        s'.tape 1 = (dispatchMs m ms').pc ∧ s'.tape 2 = (dispatchMs m ms').c1 ∧
        s'.tape 3 = (dispatchMs m ms').c2 := by
  let B : Program := Compiler.movePtr 0 4 ++ Compiler.clearHere ++
    List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr)) ++
    Compiler.ifZeroElse 4 5 6 7 8
      (Compiler.movePtr 4 0 ++ Compiler.clearHere ++ Compiler.movePtr 0 4) [] ++
    Compiler.movePtr 4 0
  have hB : Compiler.compileProgram m = ([.loop B] : Program) := by
    simp only [Compiler.compileProgram, B]
  induction hr generalizing s with
  | halt ms0 hterminal =>
      rcases runsTo_compileBody m ms0 s hsim (by exact hsim.2.2.2.2) hclean with
        ⟨s1, hb, post⟩
      have hrun0 : s1.tape 0 = 0 := by
        rw [post.2.1]
        rcases hterminal with hhalt | hnone
        · rcases dispatch_halt m ms0 hhalt with ⟨hd, hr0, hm⟩
          rw [hd, hr0]
          rfl
        · rcases dispatch_none m ms0 hnone with ⟨hd, hr0, hm⟩
          rw [hd]
          rfl
      have hcur : State.currentVal s1 = 0 := by
        simp only [State.currentVal, post.1, hrun0]
      have hstepL0 : step ([.loop B] : Program) s1 = some ([], s1) := step_loop_zero s1 B hcur
      have hloop0 : RunsTo (([.loop B] : Program), s1) s1 :=
        RunsTo.step ([.loop B] : Program) s1 s1 [] s1 hstepL0 (RunsTo.halt s1)
      have hmain : RunsTo (B ++ ([.loop B] : Program), s) s1 :=
        RunsTo_append ([.loop B] : Program) s1 s1 hb hloop0
      have hcur0 : State.currentVal s ≠ 0 := by
        simp only [State.currentVal, hsim.1, hsim.2.2.2.2]
        decide
      have hstepL : step ([.loop B] : Program) s = some (B ++ ([.loop B] : Program), s) :=
        step_loop_nonzero s B hcur0
      have hrun' : RunsTo (Compiler.compileProgram m, s) s1 := by
        rw [hB]
        exact RunsTo.step ([.loop B] : Program) s s (B ++ ([.loop B] : Program)) s1 hstepL hmain
      refine ⟨s1, hrun', ?_, ?_, ?_, ?_, ?_⟩
      · exact post.1
      · exact hrun0
      · rw [post.2.2.1]
      · rw [post.2.2.2.1]
      · rw [post.2.2.2.2.1]
  | step ms_start ms1 ms_final hstep hr' ih =>
      rcases step_getElem m ms_start ms1 hstep with ⟨instr, hget, hne, hinstr⟩
      rcases dispatchMs_step m ms_start instr hget hne with ⟨hd, hr, hm⟩
      have hsim' : SimulatesAt ms_start 0 s := by
        simpa only [SimulatesAt] using hsim
      rcases runsTo_compileBody m ms_start s hsim' (by exact hsim'.2.2.2.2) hclean with
        ⟨s1, hb, post⟩
      have hsim1 : SimulatesAt ms1 0 s1 := by
        change s1.ptr = 0 ∧ s1.tape 1 = ms1.pc ∧ s1.tape 2 = ms1.c1 ∧
          s1.tape 3 = ms1.c2 ∧ s1.tape 0 = 1
        constructor
        · exact post.1
        · constructor
          · rw [post.2.2.1]
            exact congrArg Minsky.State.pc (hm.trans hinstr)
          · constructor
            · rw [post.2.2.2.1]
              exact congrArg Minsky.State.c1 (hm.trans hinstr)
            · constructor
              · rw [post.2.2.2.2.1]
                exact congrArg Minsky.State.c2 (hm.trans hinstr)
              · rw [post.2.1, hd, hr]
                rfl
      have hclean1 : s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 := by
        exact ⟨post.2.2.2.2.2.1, post.2.2.2.2.2.2.1, post.2.2.2.2.2.2.2.1,
          post.2.2.2.2.2.2.2.2⟩
      rcases ih s1 hsim1 hclean1 with ⟨s', hrest, hpost⟩
      have hmain : RunsTo (B ++ ([.loop B] : Program), s) s' :=
        RunsTo_append ([.loop B] : Program) s1 s' hb hrest
      have hcur0 : State.currentVal s ≠ 0 := by
        simp only [State.currentVal, hsim.1, hsim.2.2.2.2]
        decide
      have hstepL : step ([.loop B] : Program) s = some (B ++ ([.loop B] : Program), s) :=
        step_loop_nonzero s B hcur0
      have hrun' : RunsTo (Compiler.compileProgram m, s) s' := by
        rw [hB]
        exact RunsTo.step ([.loop B] : Program) s s (B ++ ([.loop B] : Program)) s' hstepL hmain
      refine ⟨s', hrun', ?_, ?_, ?_, ?_, ?_⟩
      · exact hpost.1
      · exact hpost.2.1
      · exact hpost.2.2.1
      · exact hpost.2.2.2.1
      · exact hpost.2.2.2.2

/-- The final state of a Minsky run is terminal: its program counter either
    addresses a `halt` or runs off the end of the program. -/
theorem terminal_of_RunsTo (m : Minsky.Program) (ms ms_final : Minsky.State)
    (h : Minsky.RunsTo m ms ms_final) :
    (m : List Minsky.Instruction)[ms_final.pc]? = some .halt ∨
      (m : List Minsky.Instruction)[ms_final.pc]? = none := by
  induction h with
  | halt s hterminal => exact hterminal
  | step s s' s_final hstep hrest ih => exact ih

/-- Brainfuck is Turing complete: the two-counter Minsky machine is simulated
    by `Compiler.compileProgram`. -/
theorem turingCompleteness_proof : turingCompleteness := by
  unfold turingCompleteness
  intro m ms ms_final hruns
  have hsim : Simulates ms (simState ms) := simulates_simState ms
  have hclean : (simState ms).tape 5 = 0 ∧ (simState ms).tape 6 = 0 ∧
      (simState ms).tape 7 = 0 ∧ (simState ms).tape 8 = 0 := by
    simp only [simState]
    repeat' constructor <;> norm_num
  rcases runsTo_compileProgram m ms ms_final (simState ms) hruns hsim hclean with
    ⟨bfs_final, hrun, hptr, hflag, _, hc1, hc2⟩
  have hterminal : (m : List Minsky.Instruction)[ms_final.pc]? = some .halt ∨
      (m : List Minsky.Instruction)[ms_final.pc]? = none := terminal_of_RunsTo m ms ms_final hruns
  have hcount : (dispatchMs m ms_final).c1 = ms_final.c1 ∧
      (dispatchMs m ms_final).c2 = ms_final.c2 := by
    rcases hterminal with h | h
    · rcases dispatch_halt m ms_final h with ⟨_, _, hd⟩
      rw [hd]
      exact ⟨rfl, rfl⟩
    · rcases dispatch_none m ms_final h with ⟨_, _, hd⟩
      rw [hd]
      exact ⟨rfl, rfl⟩
  exact ⟨bfs_final, hrun, hptr, hflag, hc1.trans hcount.1, hc2.trans hcount.2⟩

end LeanBF
