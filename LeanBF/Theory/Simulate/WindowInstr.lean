/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.WindowMatchSkip

/-!
# The Dispatch Windows

The `inc1`, `inc2`, `jzdec1`, `jzdec2`, and `halt` dispatch windows.

## Theorems

* `runsTo_window_inc1`: The `inc1` window.
* `runsTo_window_inc2`: The `inc2` window.
* `runsTo_window_jzdec1`: The `jzdec1` window.
* `runsTo_window_jzdec2`: The `jzdec2` window.
* `runsTo_window_halt`: The `halt` window clears the running flag.
-/

namespace LeanBF

/-- The `inc1` window: if the `pc` is zero, run the `inc1` block and set
    `done`; otherwise decrement the `pc`. -/
theorem runsTo_window_inc1 (next : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.inc1 next)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 + 1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_inc1 next ms b0 hb0ptr hb0c1 hb0c2 hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = next ∧ s''.tape 2 = ms.c1 + 1 ∧
        s''.tape 3 = ms.c2 ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State := { pc := next, c1 := ms.c1 + 1, c2 := ms.c2 }
    rcases runsTo_window_match (Compiler.compileInstr (.inc1 next)) ms ms' s s'' 1
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.inc1 next)) ms s hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩

theorem runsTo_window_inc2 (next : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.inc2 next)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = next ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 + 1 ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_inc2 next ms b0 hb0ptr hb0c1 hb0c2 hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = next ∧ s''.tape 2 = ms.c1 ∧
        s''.tape 3 = ms.c2 + 1 ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State := { pc := next, c1 := ms.c1, c2 := ms.c2 + 1 }
    rcases runsTo_window_match (Compiler.compileInstr (.inc2 next)) ms ms' s s'' 1
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.inc2 next)) ms s hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩

theorem runsTo_window_jzdec1 (ifZero ifNonZero : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.jzdec1 ifZero ifNonZero)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = (if ms.c1 = 0 then ifZero else ifNonZero) ∧
          s'.tape 2 = (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_jzdec1 ifZero ifNonZero ms b0 hb0ptr hb0c1 hb0c2
        hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = (if ms.c1 = 0 then ifZero else ifNonZero) ∧
        s''.tape 2 = (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) ∧
        s''.tape 3 = ms.c2 ∧ s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State :=
      { pc := (if ms.c1 = 0 then ifZero else ifNonZero),
        c1 := (if ms.c1 = 0 then ms.c1 else ms.c1 - 1), c2 := ms.c2 }
    rcases runsTo_window_match (Compiler.compileInstr (.jzdec1 ifZero ifNonZero)) ms ms' s s'' 1
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.jzdec1 ifZero ifNonZero)) ms s
        hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩

theorem runsTo_window_jzdec2 (ifZero ifNonZero : Nat) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr (.jzdec2 ifZero ifNonZero)), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = (if ms.c2 = 0 then ifZero else ifNonZero) ∧
          s'.tape 2 = ms.c1 ∧ s'.tape 3 = (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_jzdec2 ifZero ifNonZero ms b0 hb0ptr hb0c1 hb0c2 hb0run with
      ⟨s'', hblock, hp1, hpc', hc1', hc2', hrun', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = (if ms.c2 = 0 then ifZero else ifNonZero) ∧
        s''.tape 2 = ms.c1 ∧
        s''.tape 3 = (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) ∧
        s''.tape 0 = 1 ∧ s''.tape 4 = 1 ∧
        s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · exact hc1'
      · exact hc2'
      · exact hrun'
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State :=
      { pc := (if ms.c2 = 0 then ifZero else ifNonZero),
        c1 := ms.c1, c2 := (if ms.c2 = 0 then ms.c2 else ms.c2 - 1) }
    rcases runsTo_window_match (Compiler.compileInstr (.jzdec2 ifZero ifNonZero)) ms ms' s s'' 1
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr (.jzdec2 ifZero ifNonZero)) ms s
        hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩

/-- The `halt` window: if the `pc` is zero, run the `halt` block (which clears
    the running flag) and set `done`; otherwise decrement the `pc`. -/
theorem runsTo_window_halt (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) :
    ∃ s', RunsTo (Compiler.window (Compiler.compileInstr .halt), s) s' ∧
      (if ms.pc = 0 then
        s'.ptr = 4 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 1 ∧ s'.tape 0 = 0 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0
      else
        s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
          s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
          s'.tape 7 = 0 ∧ s'.tape 8 = 0) := by
  by_cases hpc0 : ms.pc = 0
  · have hsptr : s.ptr = 4 := hsim.1
    have hspc : s.tape 1 = ms.pc := hsim.2.1
    have hsc1 : s.tape 2 = ms.c1 := hsim.2.2.1
    have hsc2 : s.tape 3 = ms.c2 := hsim.2.2.2.1
    have hsrunning : s.tape 0 = 1 := hsim.2.2.2.2
    rcases windowBlockStart_tape s with ⟨wptr, wtape1, wtape2, wtape3, wtape0, wtape4, wtape5,
      wtape6, wtape8, wtape9, wtape10, wtape12⟩
    let b0 : State := windowBlockStart s
    have hb0ptr : b0.ptr = 1 := by
      change (windowBlockStart s).ptr = 1
      rfl
    have hb0pc : b0.tape 1 = 0 := by
      change (windowBlockStart s).tape 1 = 0
      rfl
    have hb0c1 : b0.tape 2 = ms.c1 := by rw [wtape2]; exact hsc1
    have hb0c2 : b0.tape 3 = ms.c2 := by rw [wtape3]; exact hsc2
    have hb0run : b0.tape 0 = 1 := by rw [wtape0]; exact hsrunning
    have hb0tape4 : b0.tape 4 = 1 := by
      change (windowBlockStart s).tape 4 = 1
      rfl
    have hb0tape5 : b0.tape 5 = 0 := by
      change (windowBlockStart s).tape 5 = 0
      rfl
    have hb0tape6 : b0.tape 6 = 0 := by
      change (windowBlockStart s).tape 6 = 0
      rfl
    have hb0tape8 : b0.tape 8 = 0 := by
      change (windowBlockStart s).tape 8 = 0
      rfl
    have hb0tape9 : b0.tape 9 = 0 := by
      change (windowBlockStart s).tape 9 = 0
      rfl
    have hb0tape10 : b0.tape 10 = 0 := by
      change (windowBlockStart s).tape 10 = 0
      rfl
    have hb0tape12 : b0.tape 12 = 0 := by
      change (windowBlockStart s).tape 12 = 0
      rfl
    rcases runsTo_compileInstr_halt b0 hb0ptr hb0pc hb0run with
      ⟨s'', hblock, hp1, hpc', hrun0, hc1', hc2', hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
    have hpost : s''.ptr = 1 ∧ s''.tape 1 = 0 ∧ s''.tape 2 = ms.c1 ∧ s''.tape 3 = ms.c2 ∧
        s''.tape 0 = 0 ∧ s''.tape 4 = 1 ∧ s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧
        s''.tape 8 = 0 ∧
        s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0 := by
      repeat' constructor
      · exact hp1
      · exact hpc'
      · rw [hc1']
        exact hb0c1
      · rw [hc2']
        exact hb0c2
      · exact hrun0
      · rw [hp4]
        exact hb0tape4
      · rw [hp5]
        exact hb0tape5
      · rw [hp6]
        exact hb0tape6
      · rw [hp8]
        exact hb0tape8
      · rw [hp9]
        exact hb0tape9
      · rw [hp10]
        exact hb0tape10
      · rw [hp12]
        exact hb0tape12
    let ms' : Minsky.State := { pc := 0, c1 := ms.c1, c2 := ms.c2 }
    rcases runsTo_window_match (Compiler.compileInstr .halt) ms ms' s s'' 0
        hsim hdone hpc0 hblock hpost with
      ⟨s', hwin, wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨wptr, wpc, wc1, wc2, wdone, wrun, w5, w6, w7, w8⟩
  · rcases runsTo_window_skip (Compiler.compileInstr .halt) ms s hsim hdone hpc0 with
      ⟨s', hwin, kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩
    refine ⟨s', hwin, ?_⟩
    simp only [hpc0]
    exact ⟨kptr, kpc, kc1, kc2, kdone, krun, k5, k6, k7, k8⟩

end LeanBF
