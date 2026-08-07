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

/-!
# Done Windows and Dispatch

A window whose `done` flag is set runs nothing, and the flattened dispatch
over all windows of a program.

## Main definitions

* `dispatchMs`: The machine state after the flattened-window dispatch.
* `dispatchDone`: Whether a window matched and ran.
* `dispatchRunning`: Whether the machine keeps running.

## Theorems

* `runsTo_window_done'`: A window whose `done` flag is set runs nothing.
* `runsTo_windows_done`: The flattened dispatch over all windows.
-/

namespace LeanBF

/-- A window whose `done` flag is set runs nothing. -/
theorem runsTo_window_done' (block : Program) (s : State)
    (hptr : s.ptr = 4) (hdone : s.tape 4 = 1) :
    ∃ s', RunsTo (Compiler.window block, s) s' ∧
      s'.ptr = 4 ∧ s'.tape 1 = s.tape 1 ∧ s'.tape 2 = s.tape 2 ∧ s'.tape 3 = s.tape 3 ∧
        s'.tape 4 = 1 ∧ s'.tape 0 = s.tape 0 ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
        s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  let s_else : State := elseBodyState 4 5 6 7 8 1 s
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
  let innerThen : Program := Compiler.movePtr 1 4 ++ [.inc_val] ++ Compiler.movePtr 4 1 ++ block
  let tb : Program := Compiler.movePtr 4 1 ++
    Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++ Compiler.movePtr 1 4
  have hif : RunsTo (Compiler.ifZeroElse 4 5 6 7 8 tb [], s)
      (ifZeroElsePost 4 5 6 7 8 s_else) :=
    runsTo_ifZeroElse_succ 0 4 5 6 7 8 tb [] s s_else hptr hdone
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ helse h1e h2e h3e h4e
  have hprog : Compiler.window block = Compiler.ifZeroElse 4 5 6 7 8 tb [] := by
    simp only [Compiler.window, innerThen, tb, List.append_assoc]
  let a2 : State := ifZeroElsePost 4 5 6 7 8 s_else
  have ha2ptr : a2.ptr = 4 := by simp only [a2, ifZeroElsePost]
  have ha2tape1 : a2.tape 1 = s.tape 1 := by
    simp only [a2, ifZeroElsePost, s_else]
    rw [if_neg (by decide : ¬ (1 : Int) = 5), if_neg (by decide : ¬ (1 : Int) = 6),
      if_neg (by decide : ¬ (1 : Int) = 7), if_neg (by decide : ¬ (1 : Int) = 8)]
    simp only [elseBodyState]
    rw [if_neg (by decide : ¬ (1 : Int) = 4)]
    rfl
  have ha2tape2 : a2.tape 2 = s.tape 2 := by
    simp only [a2, ifZeroElsePost, s_else]
    rw [if_neg (by decide : ¬ (2 : Int) = 5), if_neg (by decide : ¬ (2 : Int) = 6),
      if_neg (by decide : ¬ (2 : Int) = 7), if_neg (by decide : ¬ (2 : Int) = 8)]
    simp only [elseBodyState]
    rw [if_neg (by decide : ¬ (2 : Int) = 4)]
    rfl
  have ha2tape3 : a2.tape 3 = s.tape 3 := by
    simp only [a2, ifZeroElsePost, s_else]
    rw [if_neg (by decide : ¬ (3 : Int) = 5), if_neg (by decide : ¬ (3 : Int) = 6),
      if_neg (by decide : ¬ (3 : Int) = 7), if_neg (by decide : ¬ (3 : Int) = 8)]
    simp only [elseBodyState]
    rw [if_neg (by decide : ¬ (3 : Int) = 4)]
    rfl
  have ha2tape4 : a2.tape 4 = 1 := by
    simp only [a2, ifZeroElsePost, s_else]
    rw [if_neg (by decide : ¬ (4 : Int) = 5), if_neg (by decide : ¬ (4 : Int) = 6),
      if_neg (by decide : ¬ (4 : Int) = 7), if_neg (by decide : ¬ (4 : Int) = 8)]
    simp only [elseBodyState]
    rw [if_true]
  have ha2run : a2.tape 0 = s.tape 0 := by
    simp only [a2, ifZeroElsePost, s_else]
    rw [if_neg (by decide : ¬ (0 : Int) = 5), if_neg (by decide : ¬ (0 : Int) = 6),
      if_neg (by decide : ¬ (0 : Int) = 7), if_neg (by decide : ¬ (0 : Int) = 8)]
    simp only [elseBodyState]
    rw [if_neg (by decide : ¬ (0 : Int) = 4)]
    rfl
  have ha2tape5 : a2.tape 5 = 0 := by simp only [a2, ifZeroElsePost]; rw [if_true]
  have ha2tape6 : a2.tape 6 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 5), if_true]
  have ha2tape7 : a2.tape 7 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (7 : Int) = 5), if_neg (by decide : ¬ (7 : Int) = 6), if_true]
  have ha2tape8 : a2.tape 8 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 5), if_neg (by decide : ¬ (8 : Int) = 6),
      if_neg (by decide : ¬ (8 : Int) = 7), if_true]
  have hwin : RunsTo (Compiler.window block, s) a2 := by
    simpa only [hprog] using hif
  exact ⟨a2, hwin, ha2ptr, ha2tape1, ha2tape2, ha2tape3, ha2tape4, ha2run, ha2tape5,
    ha2tape6, ha2tape7, ha2tape8⟩

/-- The Minsky state after the dispatch loop runs the windows for the current
    `pc`. -/
def dispatchMs (m : Minsky.Program) (ms : Minsky.State) : Minsky.State :=
  match m, ms.pc with
  | [], _ => ms
  | instr :: _, 0 => Minsky.stepInstr instr ms
  | _ :: rest, k + 1 => dispatchMs rest { ms with pc := k }

/-- Whether the dispatch loop matched an instruction (set the `done` flag). -/
def dispatchDone (m : Minsky.Program) (ms : Minsky.State) : Bool :=
  match m, ms.pc with
  | [], _ => false
  | _ :: _, 0 => true
  | _ :: rest, k + 1 => dispatchDone rest { ms with pc := k }

/-- The running flag after the dispatch loop. -/
def dispatchRunning (m : Minsky.Program) (ms : Minsky.State) : Nat :=
  match m, ms.pc with
  | [], _ => 1
  | .halt :: _, 0 => 0
  | _ :: _, 0 => 1
  | _ :: rest, k + 1 => dispatchRunning rest { ms with pc := k }

/-- With the `done` flag already set, the remaining windows do nothing. -/
theorem runsTo_windows_done (m : Minsky.Program) (ms : Minsky.State) (running : Nat)
    (s : State)
    (hptr : s.ptr = 4) (hpc : s.tape 1 = ms.pc) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = running) (hdone : s.tape 4 = 1)
    (hclean : s.tape 5 = 0 ∧ s.tape 6 = 0 ∧ s.tape 7 = 0 ∧ s.tape 8 = 0) :
    ∃ s', RunsTo (List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr)), s) s' ∧
      s'.ptr = 4 ∧ s'.tape 1 = ms.pc ∧ s'.tape 2 = ms.c1 ∧ s'.tape 3 = ms.c2 ∧
        s'.tape 4 = 1 ∧ s'.tape 0 = running ∧ s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧
        s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  induction m generalizing s with
  | nil =>
      rcases hclean with ⟨h5, h6, h7, h8⟩
      have hfl : List.flatten (([] : List Minsky.Instruction).map
          (Compiler.window ∘ Compiler.compileInstr)) = [] := by
        rfl
      refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfl]
        exact RunsTo.halt s
      · exact hptr
      · exact hpc
      · exact hc1
      · exact hc2
      · exact hdone
      · exact hrun
      · exact h5
      · exact h6
      · exact h7
      · exact h8
  | cons instr rest ih =>
      rcases runsTo_window_done' (Compiler.compileInstr instr) s hptr hdone with
        ⟨s1, hw1, hptr1, hpc1, hc11, hc21, hdone1, hrun1, h51, h61, h71, h81⟩
      rcases ih s1 hptr1 (by rw [hpc1]; exact hpc) (by rw [hc11]; exact hc1)
        (by rw [hc21]; exact hc2) (by rw [hrun1]; exact hrun) hdone1
        ⟨h51, h61, h71, h81⟩ with ⟨s', hrest, post⟩
      have hchain : RunsTo (List.flatten ((instr :: rest).map
          (Compiler.window ∘ Compiler.compileInstr)), s) s' := by
        simp only [List.map_cons, List.flatten_cons]
        exact RunsTo_append
          (List.flatten (rest.map (Compiler.window ∘ Compiler.compileInstr))) s1 s' hw1 hrest
      exact ⟨s', hchain, post⟩

end LeanBF
