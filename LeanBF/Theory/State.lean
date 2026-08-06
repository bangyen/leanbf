/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.State
import Mathlib.Tactic.Ring

/-!
# Tape Algebra

The cell operations act only on the addressed cell, and round-trip with the
current value.

## Theorems

* `currentVal_mkEmpty`: The initial cell value is `0`.
* `currentVal_modifyCell`: `modifyCell` applies `f` to the current cell.
* `currentVal_incVal`: `+` increments the current cell.
* `currentVal_decVal`: `-` decrements the current cell.
* `currentVal_incVal_decVal`: Incrementing then decrementing is the identity
  on the current value.
* `tape_modifyCell_self`: `modifyCell` writes only the addressed cell.
* `tape_modifyCell_other`: `modifyCell` leaves every other cell unchanged.
* `incPtr_tape`: `>` does not touch the tape.
* `decPtr_tape`: `<` does not touch the tape.
* `incVal_ptr`: `+` does not move the pointer.
* `decVal_ptr`: `-` does not move the pointer.
* `ptr_incPtr_decPtr`: Moving right then left returns the pointer.
-/

namespace LeanBF

/-- The initial cell value is `0`. -/
theorem currentVal_mkEmpty : State.currentVal State.mkEmpty = 0 :=
  rfl

/-- `modifyCell` applies `f` to the current cell. -/
theorem currentVal_modifyCell (s : State) (f : Nat → Nat) :
    State.currentVal (State.modifyCell s f) = f (State.currentVal s) := by
  simp only [State.currentVal, State.modifyCell]
  rfl

/-- `+` increments the current cell. -/
theorem currentVal_incVal (s : State) :
    State.currentVal (State.incVal s) = State.currentVal s + 1 := by
  rw [State.incVal, currentVal_modifyCell]

/-- `-` decrements the current cell. -/
theorem currentVal_decVal (s : State) :
    State.currentVal (State.decVal s) = State.currentVal s - 1 := by
  rw [State.decVal, currentVal_modifyCell]

/-- Incrementing then decrementing is the identity on the current value. -/
theorem currentVal_incVal_decVal (s : State) :
    State.currentVal (State.decVal (State.incVal s)) = State.currentVal s := by
  rw [currentVal_decVal, currentVal_incVal, Nat.add_sub_cancel]

/-- `modifyCell` writes only the addressed cell. -/
theorem tape_modifyCell_self (s : State) (f : Nat → Nat) :
    (State.modifyCell s f).tape s.ptr = f (s.tape s.ptr) := by
  simp only [State.modifyCell]
  rfl

/-- `modifyCell` leaves every other cell unchanged. -/
theorem tape_modifyCell_other (s : State) (f : Nat → Nat) {i : Int} (h : i ≠ s.ptr) :
    (State.modifyCell s f).tape i = s.tape i := by
  simp only [State.modifyCell, if_neg h]

/-- `>` does not touch the tape. -/
theorem incPtr_tape (s : State) : (State.incPtr s).tape = s.tape :=
  rfl

/-- `<` does not touch the tape. -/
theorem decPtr_tape (s : State) : (State.decPtr s).tape = s.tape :=
  rfl

/-- `+` does not move the pointer. -/
theorem incVal_ptr (s : State) : (State.incVal s).ptr = s.ptr :=
  rfl

/-- `-` does not move the pointer. -/
theorem decVal_ptr (s : State) : (State.decVal s).ptr = s.ptr :=
  rfl

/-- Moving right then left returns the pointer. -/
theorem ptr_incPtr_decPtr (s : State) :
    (State.decPtr (State.incPtr s)).ptr = s.ptr := by
  simp only [State.incPtr, State.decPtr]
  ring

end LeanBF
