/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Transfer

/-!
# Register Transfer Tests

Kernel re-assertions of the drain loop: its effect on a concrete program, and
the transitivity of reachability.

## Main definitions

* `drainProg`: A two-instruction drain loop followed by `halt`.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- Drain register `0` into register `1`, then halt. -/
def drainProg : Program :=
  [.jzdec 0 2 1, .inc 1 0, .halt]

/-- The loop sits at offsets `0` and `1`, as `drain_reaches` requires. -/
example : drainProg[0]? = some (Instruction.jzdec 0 2 1) := rfl

example : drainProg[1]? = some (Instruction.inc 1 0) := rfl

/-- Draining three units moves them all across. -/
example : Reaches drainProg { pc := 0, regs := fun i => if i = 0 then 3 else 0 }
    (drained 0 1 2 3 { pc := 0, regs := fun i => if i = 0 then 3 else 0 }) :=
  drain_reaches drainProg 0 1 0 2 (by decide) rfl rfl 3 _ rfl rfl

/-- The drained state holds the sum in the target and zero in the source. -/
example : (drained 0 1 2 3 { pc := 0, regs := fun i => if i = 0 then 3 else 0 }).regs 1 = 3 := rfl

example : (drained 0 1 2 3 { pc := 0, regs := fun i => if i = 0 then 3 else 0 }).regs 0 = 0 := rfl

/-- Reachability is transitive, so fragments chain. -/
example (p : Program) (a b c : State) (h1 : Reaches p a b) (h2 : Reaches p b c) :
    Reaches p a c :=
  reaches_trans h1 h2

end LeanBF.Tests
