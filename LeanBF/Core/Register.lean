/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Data.Nat.Basic

/-!
# Register Machines

A counter machine with arbitrarily many registers, generalizing
`Core.Minsky`, whose two counters are fixed in the state structure.

This exists as the middle layer of the undecidability argument. Partial
recursive functions are naturally simulated by a machine with as many
registers as the construction needs, and only afterwards are those registers
packed into two by a Gödel encoding. Trying to hit two registers directly
would mix both constructions together.

Registers are a total function `Nat → Nat` rather than a fixed tuple or a
length-indexed vector, so a program can name any register without carrying a
bound. A program only ever mentions finitely many.

## Main definitions

* `Register.State`: A program counter and a register file.
* `Register.Instruction`: Increment, jump-if-zero-else-decrement, and halt.
* `Register.Program`: A list of instructions.
* `Register.setReg`: Replace one register's value.
* `Register.step`: A single step, or `none` at a terminal program counter.
* `Register.RunsTo`: The reflexive-transitive closure of `step`.
-/

namespace LeanBF

namespace Register

/-- A register machine state: a program counter and a register file. -/
structure State where
  /-- The program counter. -/
  pc : Nat
  /-- The registers, indexed from `0`. -/
  regs : Nat → Nat
  deriving Inhabited

/-- Register machine instructions. `jzdec` tests a register, jumping when it
    is zero and decrementing it otherwise, which is the standard way to make
    a counter machine's control flow depend on its data. -/
inductive Instruction where
  | inc (r : Nat) (next : Nat) : Instruction
  | jzdec (r : Nat) (ifZero : Nat) (ifNonZero : Nat) : Instruction
  | halt : Instruction
  deriving Repr

/-- A register machine program is a list of instructions. -/
abbrev Program := List Instruction

/-- Replace the value of a single register. -/
def setReg (s : State) (r v : Nat) : State :=
  { s with regs := fun i => if i = r then v else s.regs i }

/-- A single step of the register machine, or `none` if the program counter
    is out of bounds or points at `halt`. -/
def step (p : Program) (s : State) : Option State :=
  match (p : List Instruction)[s.pc]? with
  | none => none
  | some .halt => none
  | some (.inc r next) => some { setReg s r (s.regs r + 1) with pc := next }
  | some (.jzdec r ifZero ifNonZero) =>
    if s.regs r = 0 then some { s with pc := ifZero }
    else some { setReg s r (s.regs r - 1) with pc := ifNonZero }

/-- Reflexive-transitive closure of the register machine step. -/
inductive RunsTo (p : Program) : State → State → Prop where
  | halt (s : State) :
    (p : List Instruction)[s.pc]? = some Instruction.halt ∨
    (p : List Instruction)[s.pc]? = none → RunsTo p s s
  | step (s s' s_final : State) :
    step p s = some s' → RunsTo p s' s_final → RunsTo p s s_final

end Register

end LeanBF
