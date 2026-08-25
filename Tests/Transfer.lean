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
* `tripleProg`: A scaled transfer loop moving three units per unit drained.
* `divProg`: A division loop with three jzdec slots.
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

/-- A scaled transfer loop: three increments per unit drained. -/
def tripleProg : Program :=
  [.jzdec 0 4 1, .inc 1 2, .inc 1 3, .inc 1 0, .halt]

/-- The chain instructions sit where `kdrain_reaches` requires. -/
example : tripleProg[1]? = some (Instruction.inc 1 (if 0 + 1 = 3 then 0 else 0 + 2 + 0)) := rfl

example : tripleProg[3]? = some (Instruction.inc 1 (if 2 + 1 = 3 then 0 else 0 + 2 + 2)) := rfl

/-- Draining four units at three per unit yields twelve. -/
example : (scaled 0 1 4 3 4 { pc := 0, regs := fun i => if i = 0 then 4 else 0 }).regs 1 = 12 := rfl

/-- The source is emptied. -/
example : (scaled 0 1 4 3 4 { pc := 0, regs := fun i => if i = 0 then 4 else 0 }).regs 0 = 0 := rfl

/-- Walking an increment chain raises the target by the chain's length. -/
example (p : Program) (t base k : Nat)
    (hchain : ∀ j, j < k → p[base + 1 + j]? =
      some (Instruction.inc t (if j + 1 = k then base else base + 2 + j)))
    (d j : Nat) (hjk : j + d = k) (hd : 0 < d) (s : State) (hpc : s.pc = base + 1 + j) :
    Reaches p s (bumped t d base s) :=
  inc_chain p t base k hchain d j hjk hd s hpc

/-- A division loop: three jzdec slots, then an increment. -/
def divProg : Program :=
  [.jzdec 0 4 1, .jzdec 0 5 2, .jzdec 0 6 3, .inc 1 0, .halt, .halt, .halt]

/-- The chain slots sit where `div_reaches` requires, with exits at `4 + j`. -/
example : divProg[0]? = some (Instruction.jzdec 0 (4 + 0) (0 + 0 + 1)) := rfl

example : divProg[2]? = some (Instruction.jzdec 0 (4 + 2) (0 + 2 + 1)) := rfl

/-- The increment sits just past the chain. -/
example : divProg[3]? = some (Instruction.inc 1 0) := rfl

/-- Dividing seven by three gives a quotient of two and a remainder of one,
    so the loop stops at exit `4 + 1` with the target raised twice. -/
example : (divided 0 1 4 2 1 { pc := 0, regs := fun i => if i = 0 then 7 else 0 }).pc = 5 := rfl

example : (divided 0 1 4 2 1 { pc := 0, regs := fun i => if i = 0 then 7 else 0 }).regs 1 = 2 := rfl

/-- Exact division stops at the first exit, which is the divisibility test. -/
example : (divided 0 1 4 2 0 { pc := 0, regs := fun i => if i = 0 then 6 else 0 }).pc = 4 := rfl

/-- The source is emptied either way. -/
example : (divided 0 1 4 2 1 { pc := 0, regs := fun i => if i = 0 then 7 else 0 }).regs 0 = 0 := rfl

end LeanBF.Tests
