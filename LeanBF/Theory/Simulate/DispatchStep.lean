/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.Basics
import LeanBF.Theory.Simulate.CompileInstr
import LeanBF.Theory.Simulate.CompileInstrJzdec1
import LeanBF.Theory.Simulate.CompileInstrJzdec2
import LeanBF.Theory.Simulate.JzdecThenElse
import LeanBF.Theory.Simulate.WindowDone
import LeanBF.Theory.Simulate.WindowInc
import LeanBF.Theory.Simulate.WindowJzdecHalt
import LeanBF.Theory.Simulate.WindowMatch
import LeanBF.Theory.Simulate.WindowSkip

/-!
# Dispatch Step

The `stepInstr` field facts and the dispatch lemmas: a matching window
changes the state exactly as the instruction does, and the dispatch loop
runs exactly the matching window.

## Theorems

* `stepInstr_jzdec1_pc`: The jzdec1 pc update.
* `stepInstr_jzdec1_c1`: The jzdec1 c1 update.
* `stepInstr_jzdec1_c2`: The jzdec1 c2 update.
* `stepInstr_jzdec2_pc`: The jzdec2 pc update.
* `stepInstr_jzdec2_c1`: The jzdec2 c1 update.
* `stepInstr_jzdec2_c2`: The jzdec2 c2 update.
* `dispatchDone_succ`: The dispatch on a non-zero program counter.
* `dispatchRunning_succ`: The dispatch on a non-zero program counter.
* `dispatchMs_succ`: The dispatch on a non-zero program counter.
* `runsTo_dispatch`: The flattened window dispatch runs exactly the matching
  window.
-/

namespace LeanBF

theorem stepInstr_jzdec1_pc (ms : Minsky.State) (ifZero ifNonZero : Nat) :
    (Minsky.stepInstr (.jzdec1 ifZero ifNonZero) ms).pc =
      (if ms.c1 = 0 then ifZero else ifNonZero) := by
  by_cases hc : ms.c1 = 0 <;> simp only [Minsky.stepInstr, hc, if_true, if_false]

theorem stepInstr_jzdec1_c1 (ms : Minsky.State) (ifZero ifNonZero : Nat) :
    (Minsky.stepInstr (.jzdec1 ifZero ifNonZero) ms).c1 =
      (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) := by
  by_cases hc : ms.c1 = 0 <;> simp only [Minsky.stepInstr, hc, if_true, if_false]

theorem stepInstr_jzdec1_c2 (ms : Minsky.State) (ifZero ifNonZero : Nat) :
    (Minsky.stepInstr (.jzdec1 ifZero ifNonZero) ms).c2 = ms.c2 := by
  by_cases hc : ms.c1 = 0 <;> simp only [Minsky.stepInstr, hc, if_true, if_false]

theorem stepInstr_jzdec2_pc (ms : Minsky.State) (ifZero ifNonZero : Nat) :
    (Minsky.stepInstr (.jzdec2 ifZero ifNonZero) ms).pc =
      (if ms.c2 = 0 then ifZero else ifNonZero) := by
  by_cases hc : ms.c2 = 0 <;> simp only [Minsky.stepInstr, hc, if_true, if_false]

theorem stepInstr_jzdec2_c1 (ms : Minsky.State) (ifZero ifNonZero : Nat) :
    (Minsky.stepInstr (.jzdec2 ifZero ifNonZero) ms).c1 = ms.c1 := by
  by_cases hc : ms.c2 = 0 <;> simp only [Minsky.stepInstr, hc, if_true, if_false]

theorem stepInstr_jzdec2_c2 (ms : Minsky.State) (ifZero ifNonZero : Nat) :
    (Minsky.stepInstr (.jzdec2 ifZero ifNonZero) ms).c2 =
      (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) := by
  by_cases hc : ms.c2 = 0 <;> simp only [Minsky.stepInstr, hc, if_true, if_false]

theorem dispatchDone_succ (instr : Minsky.Instruction) (rest : Minsky.Program)
    (ms : Minsky.State) (k : Nat) (hpc : ms.pc = Nat.succ k) :
    dispatchDone (instr :: rest) ms = dispatchDone rest { ms with pc := k } := by
  simp only [hpc, Nat.succ_eq_add_one, Nat.add_right_cancel_iff, dispatchDone]

theorem dispatchRunning_succ (instr : Minsky.Instruction) (rest : Minsky.Program)
    (ms : Minsky.State) (k : Nat) (hpc : ms.pc = Nat.succ k) :
    dispatchRunning (instr :: rest) ms = dispatchRunning rest { ms with pc := k } := by
  simp only [hpc, Nat.succ_eq_add_one, Nat.add_right_cancel_iff, dispatchRunning]

theorem dispatchMs_succ (instr : Minsky.Instruction) (rest : Minsky.Program)
    (ms : Minsky.State) (k : Nat) (hpc : ms.pc = Nat.succ k) :
    dispatchMs (instr :: rest) ms = dispatchMs rest { ms with pc := k } := by
  simp only [hpc, Nat.succ_eq_add_one, Nat.add_right_cancel_iff, dispatchMs]

theorem runsTo_dispatch (m : Minsky.Program) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0)
    (hclean : s.tape 5 = 0 ∧ s.tape 6 = 0 ∧ s.tape 7 = 0 ∧ s.tape 8 = 0) :
    ∃ s', RunsTo (List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr)), s) s' ∧
      s'.ptr = 4 ∧ s'.tape 4 = (if dispatchDone m ms then 1 else 0) ∧
        s'.tape 0 = dispatchRunning m ms ∧ s'.tape 1 = (dispatchMs m ms).pc ∧
        s'.tape 2 = (dispatchMs m ms).c1 ∧ s'.tape 3 = (dispatchMs m ms).c2 ∧
        s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧ s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  induction m generalizing s ms with
  | nil =>
      rcases hsim with ⟨hsptr, hspc, hsc1, hsc2, hsrunning⟩
      rcases hclean with ⟨h5, h6, h7, h8⟩
      have hfl : List.flatten (([] : List Minsky.Instruction).map
          (Compiler.window ∘ Compiler.compileInstr)) = [] := by
        rfl
      refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfl]
        exact RunsTo.halt s
      · exact hsptr
      · simp only [dispatchDone]
        exact hdone
      · simp only [dispatchRunning]
        exact hsrunning
      · simp only [dispatchMs]
        exact hspc
      · simp only [dispatchMs]
        exact hsc1
      · simp only [dispatchMs]
        exact hsc2
      · exact h5
      · exact h6
      · exact h7
      · exact h8
  | cons instr rest ih =>
      cases hpc : ms.pc with
      | zero =>
          cases instr with
          | inc1 next =>
              rcases runsTo_window_inc1 next ms s hsim hdone with ⟨s1, hw1, hpost1⟩
              have hpost1' : s1.ptr = 4 ∧ s1.tape 1 = next ∧ s1.tape 2 = ms.c1 + 1 ∧
                  s1.tape 3 = ms.c2 ∧ s1.tape 4 = 1 ∧ s1.tape 0 = 1 ∧
                  s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 := by
                simpa only [hpc] using hpost1
              rcases hpost1' with ⟨hptr1, hpc1, hc11, hc21, hdone1, hrun1, h51, h61, h71, h81⟩
              let ms' : Minsky.State := { pc := next, c1 := ms.c1 + 1, c2 := ms.c2 }
              rcases runsTo_windows_done rest ms' 1 s1 hptr1 hpc1 hc11 hc21 hrun1 hdone1
                ⟨h51, h61, h71, h81⟩ with ⟨s', hrest, post⟩
              have hchain : RunsTo (List.flatten (((.inc1 next) :: rest).map
                  (Compiler.window ∘ Compiler.compileInstr)), s) s' := by
                simp only [List.map_cons, List.flatten_cons]
                exact RunsTo_append
                  (List.flatten (rest.map (Compiler.window ∘ Compiler.compileInstr)))
                  s1 s' hw1 hrest
              refine ⟨s', hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact post.1
              · simp only [dispatchDone, hpc]
                exact post.2.2.2.2.1
              · simp only [dispatchRunning, hpc]
                exact post.2.2.2.2.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.2.2.1
              · exact post.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.2
          | inc2 next =>
              rcases runsTo_window_inc2 next ms s hsim hdone with ⟨s1, hw1, hpost1⟩
              have hpost1' : s1.ptr = 4 ∧ s1.tape 1 = next ∧ s1.tape 2 = ms.c1 ∧
                  s1.tape 3 = ms.c2 + 1 ∧ s1.tape 4 = 1 ∧ s1.tape 0 = 1 ∧
                  s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 := by
                simpa only [hpc] using hpost1
              rcases hpost1' with ⟨hptr1, hpc1, hc11, hc21, hdone1, hrun1, h51, h61, h71, h81⟩
              let ms' : Minsky.State := { pc := next, c1 := ms.c1, c2 := ms.c2 + 1 }
              rcases runsTo_windows_done rest ms' 1 s1 hptr1 hpc1 hc11 hc21 hrun1 hdone1
                ⟨h51, h61, h71, h81⟩ with ⟨s', hrest, post⟩
              have hchain : RunsTo (List.flatten (((.inc2 next) :: rest).map
                  (Compiler.window ∘ Compiler.compileInstr)), s) s' := by
                simp only [List.map_cons, List.flatten_cons]
                exact RunsTo_append
                  (List.flatten (rest.map (Compiler.window ∘ Compiler.compileInstr)))
                  s1 s' hw1 hrest
              refine ⟨s', hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact post.1
              · simp only [dispatchDone, hpc]
                exact post.2.2.2.2.1
              · simp only [dispatchRunning, hpc]
                exact post.2.2.2.2.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.2.2.1
              · exact post.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.2
          | jzdec1 ifZero ifNonZero =>
              rcases runsTo_window_jzdec1 ifZero ifNonZero ms s hsim hdone with
                ⟨s1, hw1, hpost1⟩
              have hpost1' : s1.ptr = 4 ∧
                  s1.tape 1 = (if ms.c1 = 0 then ifZero else ifNonZero) ∧
                  s1.tape 2 = (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) ∧
                  s1.tape 3 = ms.c2 ∧ s1.tape 4 = 1 ∧ s1.tape 0 = 1 ∧
                  s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 := by
                simpa only [hpc] using hpost1
              rcases hpost1' with ⟨hptr1, hpc1, hc11, hc21, hdone1, hrun1, h51, h61, h71, h81⟩
              let ms' : Minsky.State :=
                { pc := (if ms.c1 = 0 then ifZero else ifNonZero),
                  c1 := (if ms.c1 = 0 then ms.c1 else ms.c1 - 1), c2 := ms.c2 }
              rcases runsTo_windows_done rest ms' 1 s1 hptr1 hpc1 hc11 hc21 hrun1 hdone1
                ⟨h51, h61, h71, h81⟩ with ⟨s', hrest, post⟩
              have hchain : RunsTo (List.flatten (((.jzdec1 ifZero ifNonZero) :: rest).map
                  (Compiler.window ∘ Compiler.compileInstr)), s) s' := by
                simp only [List.map_cons, List.flatten_cons]
                exact RunsTo_append
                  (List.flatten (rest.map (Compiler.window ∘ Compiler.compileInstr)))
                  s1 s' hw1 hrest
              refine ⟨s', hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact post.1
              · simp only [dispatchDone, hpc]
                exact post.2.2.2.2.1
              · simp only [dispatchRunning, hpc]
                exact post.2.2.2.2.2.1
              · rw [show s'.tape 1 = ms'.pc from post.2.1]
                simp only [dispatchMs, hpc, stepInstr_jzdec1_pc, ms']
              · rw [show s'.tape 2 = ms'.c1 from post.2.2.1]
                simp only [dispatchMs, hpc, stepInstr_jzdec1_c1, ms']
              · rw [show s'.tape 3 = ms'.c2 from post.2.2.2.1]
                simp only [dispatchMs, hpc, stepInstr_jzdec1_c2, ms']
              · exact post.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.2
          | jzdec2 ifZero ifNonZero =>
              rcases runsTo_window_jzdec2 ifZero ifNonZero ms s hsim hdone with
                ⟨s1, hw1, hpost1⟩
              have hpost1' : s1.ptr = 4 ∧
                  s1.tape 1 = (if ms.c2 = 0 then ifZero else ifNonZero) ∧
                  s1.tape 2 = ms.c1 ∧
                  s1.tape 3 = (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) ∧
                  s1.tape 4 = 1 ∧ s1.tape 0 = 1 ∧
                  s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 := by
                simpa only [hpc] using hpost1
              rcases hpost1' with ⟨hptr1, hpc1, hc11, hc21, hdone1, hrun1, h51, h61, h71, h81⟩
              let ms' : Minsky.State :=
                { pc := (if ms.c2 = 0 then ifZero else ifNonZero),
                  c1 := ms.c1, c2 := (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) }
              rcases runsTo_windows_done rest ms' 1 s1 hptr1 hpc1 hc11 hc21 hrun1 hdone1
                ⟨h51, h61, h71, h81⟩ with ⟨s', hrest, post⟩
              have hchain : RunsTo (List.flatten (((.jzdec2 ifZero ifNonZero) :: rest).map
                  (Compiler.window ∘ Compiler.compileInstr)), s) s' := by
                simp only [List.map_cons, List.flatten_cons]
                exact RunsTo_append
                  (List.flatten (rest.map (Compiler.window ∘ Compiler.compileInstr)))
                  s1 s' hw1 hrest
              refine ⟨s', hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact post.1
              · simp only [dispatchDone, hpc]
                exact post.2.2.2.2.1
              · simp only [dispatchRunning, hpc]
                exact post.2.2.2.2.2.1
              · rw [show s'.tape 1 = ms'.pc from post.2.1]
                simp only [dispatchMs, hpc, stepInstr_jzdec2_pc, ms']
              · rw [show s'.tape 2 = ms'.c1 from post.2.2.1]
                simp only [dispatchMs, hpc, stepInstr_jzdec2_c1, ms']
              · rw [show s'.tape 3 = ms'.c2 from post.2.2.2.1]
                simp only [dispatchMs, hpc, stepInstr_jzdec2_c2, ms']
              · exact post.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.2
          | halt =>
              rcases runsTo_window_halt ms s hsim hdone with ⟨s1, hw1, hpost1⟩
              have hpost1' : s1.ptr = 4 ∧ s1.tape 1 = 0 ∧ s1.tape 2 = ms.c1 ∧
                  s1.tape 3 = ms.c2 ∧ s1.tape 4 = 1 ∧ s1.tape 0 = 0 ∧
                  s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 := by
                simpa only [hpc] using hpost1
              rcases hpost1' with ⟨hptr1, hpc1, hc11, hc21, hdone1, hrun1, h51, h61, h71, h81⟩
              let ms' : Minsky.State := { pc := 0, c1 := ms.c1, c2 := ms.c2 }
              rcases runsTo_windows_done rest ms' 0 s1 hptr1 hpc1 hc11 hc21 hrun1 hdone1
                ⟨h51, h61, h71, h81⟩ with ⟨s', hrest, post⟩
              have hchain : RunsTo (List.flatten ((.halt :: rest).map
                  (Compiler.window ∘ Compiler.compileInstr)), s) s' := by
                simp only [List.map_cons, List.flatten_cons]
                exact RunsTo_append
                  (List.flatten (rest.map (Compiler.window ∘ Compiler.compileInstr)))
                  s1 s' hw1 hrest
              refine ⟨s', hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact post.1
              · simp only [dispatchDone, hpc]
                exact post.2.2.2.2.1
              · simp only [dispatchRunning, hpc]
                exact post.2.2.2.2.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.2.1
              · simp only [dispatchMs, hpc, Minsky.stepInstr]
                exact post.2.2.2.1
              · exact post.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.1
              · exact post.2.2.2.2.2.2.2.2.2
      | succ k =>
          have hpc_ne : ms.pc ≠ 0 := by
            rw [hpc]
            omega
          rcases runsTo_window_skip (Compiler.compileInstr instr) ms s hsim hdone hpc_ne with
            ⟨s1, hw1, hptr1, hpc1, hc11, hc21, hdone1, hrun1, h51, h61, h71, h81⟩
          have hk : ms.pc - 1 = k := by
            rw [hpc]
            omega
          have hsim1 : SimulatesAt { ms with pc := k } 4 s1 := by
            simp only [SimulatesAt]
            constructor
            · exact hptr1
            · constructor
              · rw [hpc1]
                exact hk
              · constructor
                · exact hc11
                · constructor
                  · exact hc21
                  · exact hrun1
          have hclean1 : s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 := by
            exact ⟨h51, h61, h71, h81⟩
          rcases ih { ms with pc := k } s1 hsim1 hdone1 hclean1 with ⟨s', hrest, post⟩
          have hchain : RunsTo (List.flatten ((instr :: rest).map
              (Compiler.window ∘ Compiler.compileInstr)), s) s' := by
            simp only [List.map_cons, List.flatten_cons]
            exact RunsTo_append
              (List.flatten (rest.map (Compiler.window ∘ Compiler.compileInstr))) s1 s' hw1 hrest
          refine ⟨s', hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact post.1
          · rw [dispatchDone_succ instr rest ms k hpc]
            exact post.2.1
          · rw [dispatchRunning_succ instr rest ms k hpc]
            exact post.2.2.1
          · rw [dispatchMs_succ instr rest ms k hpc]
            exact post.2.2.2.1
          · rw [dispatchMs_succ instr rest ms k hpc]
            exact post.2.2.2.2.1
          · rw [dispatchMs_succ instr rest ms k hpc]
            exact post.2.2.2.2.2.1
          · exact post.2.2.2.2.2.2.1
          · exact post.2.2.2.2.2.2.2.1
          · exact post.2.2.2.2.2.2.2.2.1
          · exact post.2.2.2.2.2.2.2.2.2

end LeanBF
