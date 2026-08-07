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
import LeanBF.Theory.Simulate.DispatchStep
import LeanBF.Theory.Simulate.JzdecThenElse
import LeanBF.Theory.Simulate.WindowDone
import LeanBF.Theory.Simulate.WindowInc
import LeanBF.Theory.Simulate.WindowJzdecHalt
import LeanBF.Theory.Simulate.WindowMatch
import LeanBF.Theory.Simulate.WindowSkip

/-!
# Dispatch Lemmas

The dispatch cases: a running machine steps, a halt stops, and an
out-of-range program counter falls off.

## Theorems

* `stepInstr_pc_irrelevant`: `stepInstr` is independent of the program
  counter except for halt.
* `dispatchMs_step`: Only the pc-matching instruction changes the state.
* `dispatch_halt`: A `halt` instruction stops the machine.
* `dispatch_none`: An out-of-range program counter falls off the program.
-/

namespace LeanBF

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

end LeanBF
