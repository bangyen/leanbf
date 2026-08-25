/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packed

/-!
# Packed Register Tests

Kernel re-assertions of the multiplication fragment: its instruction layout,
its effect, and that the scratch register is returned to zero.

## Main definitions

* `mulProg`: A multiply-by-three fragment using register `1` as scratch.
* `divProg2`: A divide-by-two fragment using register `1` to bank groups.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- Multiply register `0` by three, draining through register `1`. -/
def mulProg : Program :=
  [.jzdec 0 2 1, .inc 1 0, .jzdec 1 6 3, .inc 0 4, .inc 0 5, .inc 0 2, .halt]

/-- The drain loop sits at `0` and `1`. -/
example : mulProg[0]? = some (Instruction.jzdec 0 2 (0 + 1)) := rfl

example : mulProg[1]? = some (Instruction.inc 1 0) := rfl

/-- The scaled transfer starts at `2`, with its chain at `3`, `4`, `5`. -/
example : mulProg[2]? = some (Instruction.jzdec 1 6 (2 + 1)) := rfl

example : mulProg[5]? = some (Instruction.inc 0 (if 2 + 1 = 3 then 2 else 2 + 2 + 2)) := rfl

/-- Multiplying five by three gives fifteen. -/
example : (multiplied 0 1 6 3 5 { pc := 0, regs := fun i => if i = 0 then 5 else 0 }).regs 0
    = 15 := rfl

/-- The scratch register is returned to zero, so fragments can be chained. -/
example : (multiplied 0 1 6 3 5 { pc := 0, regs := fun i => if i = 0 then 5 else 0 }).regs 1
    = 0 := rfl

/-- Multiplying zero leaves zero. -/
example : (multiplied 0 1 6 3 0 { pc := 0, regs := fun _ => 0 }).regs 0 = 0 := rfl

/-- Divide register `0` by two, banking through register `1`. -/
def divProg2 : Program :=
  [.jzdec 0 3 1, .jzdec 0 4 2, .inc 1 0, .jzdec 1 6 5, .halt, .inc 0 3, .halt]

/-- The chain slots exit at `3 + j`, so the drain-back sits at the `j = 0`
    exit and fires only on exact division. -/
example : divProg2[0]? = some (Instruction.jzdec 0 (3 + 0) (0 + 0 + 1)) := rfl

example : divProg2[1]? = some (Instruction.jzdec 0 (3 + 1) (0 + 1 + 1)) := rfl

/-- The remainder exit is a separate address from the exact one. -/
example : divProg2[4]? = some Instruction.halt := rfl

/-- The increment banking each group sits just past the chain. -/
example : divProg2[2]? = some (Instruction.inc 1 0) := rfl

/-- The drain-back occupies the zero-remainder exit. -/
example : divProg2[3]? = some (Instruction.jzdec 1 6 (3 + 1 + 1)) := rfl

/-- Dividing six by two gives three, with the scratch returned to zero. -/
example : (divExact 0 1 6 3 { pc := 0, regs := fun i => if i = 0 then 6 else 0 }).regs 0 = 3 := rfl

example : (divExact 0 1 6 3 { pc := 0, regs := fun i => if i = 0 then 6 else 0 }).regs 1 = 0 := rfl

/-- It finishes at the exit shared by both composed fragments. -/
example : (divExact 0 1 6 3 { pc := 0, regs := fun i => if i = 0 then 6 else 0 }).pc = 6 := rfl

end LeanBF.Tests
