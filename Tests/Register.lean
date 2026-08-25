/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Register

/-!
# Register Machine Tests

Kernel re-assertions of the register machine on concrete programs: the step
function, the register update, and a short run to halting.

## Main definitions

* `zeroState`: The state with every register at zero.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- The empty register file. -/
def zeroState : State := { pc := 0, regs := fun _ => 0 }

example : (setReg zeroState 3 7).regs 3 = 7 := rfl

/-- Setting one register leaves the others alone. -/
example : (setReg zeroState 3 7).regs 4 = 0 := rfl

/-- `inc` raises its register and jumps. -/
example : step [.inc 2 1, .halt] zeroState
    = some { pc := 1, regs := fun i => if i = 2 then 1 else 0 } := rfl

/-- `jzdec` takes the zero branch on an empty register. -/
example : step [.jzdec 0 5 9, .halt] zeroState = some { zeroState with pc := 5 } := rfl

/-- `jzdec` decrements and takes the other branch when the register is set. -/
example : (step [.jzdec 0 5 9] { pc := 0, regs := fun _ => 2 }).map (fun s => (s.pc, s.regs 0))
    = some (9, 1) := rfl

/-- A program halts when the counter reaches `halt`. -/
example : step [Instruction.halt] zeroState = none := rfl

/-- And when the counter runs off the end. -/
example : step ([] : Program) zeroState = none := rfl

/-- Adding two to a register, then halting. -/
example : ∃ s', RunsTo [.inc 0 1, .inc 0 2, .halt] zeroState s' ∧
    s'.pc = 2 ∧ s'.regs 0 = 2 := by
  refine ⟨_, RunsTo.step _ _ _ rfl (RunsTo.step _ _ _ rfl (RunsTo.halt _ (Or.inl rfl))), ?_, ?_⟩
  · rfl
  · rfl

end LeanBF.Tests
