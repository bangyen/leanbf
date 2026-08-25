/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.WindowInstr

/-!
# Dispatch

The done windows, the flattened dispatch over all windows, the dispatch
lemmas, and the dispatch loop running exactly the matching window.

## Main definitions

* `dispatchMs`: The machine state after the flattened-window dispatch.
* `dispatchDone`: Whether a window matched and ran.
* `dispatchRunning`: Whether the machine keeps running.

## Theorems

* `runsTo_window_done'`: A window whose done flag is set runs nothing.
* `runsTo_windows_done`: The flattened dispatch over all windows.
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
* `stepInstr_pc_irrelevant`: `stepInstr` is independent of the program
  counter except for halt.
* `dispatchMs_step`: Only the pc-matching instruction changes the state.
* `dispatch_halt`: A `halt` instruction stops the machine.
* `dispatch_none`: An out-of-range program counter falls off the program.
* `step_getElem`: A running machine's current instruction steps to its
  stepInstr effect.
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

theorem stepInstr_pc_irrelevant (instr : Minsky.Instruction) (ms : Minsky.State) (k : Nat)
    (hne : instr ≠ .halt) :
    Minsky.stepInstr instr { ms with pc := k } = Minsky.stepInstr instr ms := by
  cases instr with
  | inc1 next => rfl
  | inc2 next => rfl
  | jzdec1 ifZero ifNonZero => rfl
  | jzdec2 ifZero ifNonZero => rfl
  | halt => exact False.elim (hne rfl)

theorem dispatchMs_step (m : Minsky.Program) (ms : Minsky.State) (instr : Minsky.Instruction)
    (h : (m : List Minsky.Instruction)[ms.pc]? = some instr) (hne : instr ≠ .halt) :
    dispatchDone m ms = true ∧ dispatchRunning m ms = 1 ∧
      dispatchMs m ms = Minsky.stepInstr instr ms := by
  induction m generalizing ms hne with
  | nil =>
      simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h
  | cons head tail ih =>
      cases hpc : ms.pc with
      | zero =>
          have hhead : head = instr := by
            simp only [hpc, List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
              or_true, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h
            exact h
          rw [hhead]
          cases instr with
          | inc1 next =>
              unfold dispatchDone dispatchRunning dispatchMs
              rw [hpc]
              exact ⟨rfl, rfl, rfl⟩
          | inc2 next =>
              unfold dispatchDone dispatchRunning dispatchMs
              rw [hpc]
              exact ⟨rfl, rfl, rfl⟩
          | jzdec1 ifZero ifNonZero =>
              unfold dispatchDone dispatchRunning dispatchMs
              rw [hpc]
              exact ⟨rfl, rfl, rfl⟩
          | jzdec2 ifZero ifNonZero =>
              unfold dispatchDone dispatchRunning dispatchMs
              rw [hpc]
              exact ⟨rfl, rfl, rfl⟩
          | halt => exact False.elim (hne rfl)
      | succ k =>
          have hk : (tail : List Minsky.Instruction)[k]? = some instr := by
            simp only [hpc, List.getElem?_cons_succ] at h
            exact h
          rcases ih ({ ms with pc := k } : Minsky.State) hk hne with ⟨hd, hr, hm⟩
          have hres : dispatchMs tail ({ ms with pc := k }) =
              Minsky.stepInstr instr ms := by
            rw [hm, stepInstr_pc_irrelevant instr ms k hne]
          rw [dispatchDone_succ head tail ms k hpc, dispatchRunning_succ head tail ms k hpc,
            dispatchMs_succ head tail ms k hpc]
          exact ⟨hd, hr, hres⟩

theorem dispatch_halt (m : Minsky.Program) (ms : Minsky.State)
    (h : (m : List Minsky.Instruction)[ms.pc]? = some .halt) :
    dispatchDone m ms = true ∧ dispatchRunning m ms = 0 ∧
      dispatchMs m ms = { ms with pc := 0 } := by
  induction m generalizing ms with
  | nil =>
      simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h
  | cons head tail ih =>
      cases hpc : ms.pc with
      | zero =>
          have hhead : head = .halt := by
            simp only [hpc, List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
              or_true, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h
            exact h
          rw [hhead]
          constructor
          · unfold dispatchDone
            rw [hpc]
          · constructor
            · unfold dispatchRunning
              rw [hpc]
            · unfold dispatchMs
              rw [hpc]
              change Minsky.stepInstr .halt ms = { ms with pc := 0 }
              unfold Minsky.stepInstr
              cases ms with
              | mk pc c1 c2 =>
                  change Minsky.State.mk pc c1 c2 = Minsky.State.mk 0 c1 c2
                  congr
      | succ k =>
          have hk : (tail : List Minsky.Instruction)[k]? = some .halt := by
            simp only [hpc, List.getElem?_cons_succ] at h
            exact h
          rcases ih ({ ms with pc := k } : Minsky.State) hk with ⟨hd, hr, hm⟩
          rw [dispatchDone_succ head tail ms k hpc, dispatchRunning_succ head tail ms k hpc,
            dispatchMs_succ head tail ms k hpc]
          exact ⟨hd, hr, hm⟩

theorem dispatch_none (m : Minsky.Program) (ms : Minsky.State)
    (h : (m : List Minsky.Instruction)[ms.pc]? = none) :
    dispatchDone m ms = false ∧ dispatchRunning m ms = 1 ∧
      dispatchMs m ms = { ms with pc := ms.pc - m.length } := by
  induction m generalizing ms with
  | nil =>
      simp only [dispatchDone, dispatchRunning, dispatchMs, List.length_nil, tsub_zero, and_self]
  | cons head tail ih =>
      cases hpc : ms.pc with
      | zero =>
          simp only [hpc, List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
            getElem?_pos, List.getElem_cons_zero, reduceCtorEq] at h
      | succ k =>
          have hk : (tail : List Minsky.Instruction)[k]? = none := by
            simp only [hpc, List.getElem?_cons_succ] at h
            exact h
          rcases ih ({ ms with pc := k } : Minsky.State) hk with ⟨hd, hr, hm⟩
          rw [dispatchDone_succ head tail ms k hpc, dispatchRunning_succ head tail ms k hpc,
            dispatchMs_succ head tail ms k hpc]
          rw [show k + 1 - (head :: tail).length = k - tail.length
          from by simp only [List.length_cons, Nat.succ_sub_succ]]
          exact ⟨hd, hr, hm⟩

lemma step_getElem (m : Minsky.Program) (ms ms' : Minsky.State)
    (h : Minsky.step m ms = some ms') :
    ∃ instr : Minsky.Instruction, (m : List Minsky.Instruction)[ms.pc]? = some instr ∧
      instr ≠ .halt ∧ Minsky.stepInstr instr ms = ms' := by
  unfold Minsky.step at h
  cases hpc : (m : List Minsky.Instruction)[ms.pc]? with
  | none =>
      rw [hpc] at h
      cases h
  | some ins =>
      cases ins with
      | inc1 next =>
          rw [hpc] at h
          simp only [Option.some.injEq] at h
          have hne' : (.inc1 next : Minsky.Instruction) ≠ .halt := by
            intro h'
            cases h'
          exact ⟨.inc1 next, rfl, hne', h⟩
      | inc2 next =>
          rw [hpc] at h
          simp only [Option.some.injEq] at h
          have hne' : (.inc2 next : Minsky.Instruction) ≠ .halt := by
            intro h'
            cases h'
          exact ⟨.inc2 next, rfl, hne', h⟩
      | jzdec1 ifZero ifNonZero =>
          rw [hpc] at h
          have hstep : Minsky.stepInstr (.jzdec1 ifZero ifNonZero) ms = ms' := by
            by_cases hc : ms.c1 = 0
            <;> simp only [hc, reduceIte, Option.some.injEq, Minsky.stepInstr] at h ⊢
            <;> exact h
          have hne' : (.jzdec1 ifZero ifNonZero : Minsky.Instruction) ≠ .halt := by
            intro h'
            cases h'
          exact ⟨.jzdec1 ifZero ifNonZero, rfl, hne', hstep⟩
      | jzdec2 ifZero ifNonZero =>
          rw [hpc] at h
          have hstep : Minsky.stepInstr (.jzdec2 ifZero ifNonZero) ms = ms' := by
            by_cases hc : ms.c2 = 0
            <;> simp only [hc, reduceIte, Option.some.injEq, Minsky.stepInstr] at h ⊢
            <;> exact h
          have hne' : (.jzdec2 ifZero ifNonZero : Minsky.Instruction) ≠ .halt := by
            intro h'
            cases h'
          exact ⟨.jzdec2 ifZero ifNonZero, rfl, hne', hstep⟩
      | halt =>
          rw [hpc] at h
          cases h

end LeanBF
