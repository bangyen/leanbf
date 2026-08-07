/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.Basics
import LeanBF.Theory.Simulate.CompileInstr
import LeanBF.Theory.Simulate.JzdecThenElse
import LeanBF.Theory.Simulate.CompileInstrJzdec1
import LeanBF.Theory.Simulate.CompileInstrJzdec2
import LeanBF.Theory.Simulate.WindowMatch
import LeanBF.Theory.Simulate.WindowSkip
import LeanBF.Theory.Simulate.WindowInc
import LeanBF.Theory.Simulate.WindowJzdecHalt
import LeanBF.Theory.Simulate.WindowDone
import LeanBF.Theory.Simulate.DispatchStep
import LeanBF.Theory.Simulate.DispatchLemmas
import LeanBF.Theory.Simulate.CompileBody

/-!
# Compile Program and Completeness

The compiled program runs a Minsky machine to completion, and the
`turingCompleteness` proof.

## Theorems

* `runsTo_compileProgram`: The compiled program runs the Minsky machine and
  clears the running flag.
* `turingCompleteness_proof`: The proof of `turingCompleteness`.
-/

namespace LeanBF

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
    ⟨bfs_final, hrun, hpost⟩
  exact ⟨bfs_final, hrun⟩

end LeanBF
