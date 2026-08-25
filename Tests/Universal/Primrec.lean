/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Universal.Primrec

/-!
# Primitive Recursive Case Tests

Kernel re-assertions of the case discharges, stated in the exact forms the
constructors of `Nat.Primrec` demand.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- The `left` constructor's function is built. -/
example : Builds (fun n => n.unpair.1) := builds_left

/-- And the `right` constructor's. -/
example : Builds (fun n => n.unpair.2) := builds_right

/-- These are the shapes the inductive actually uses, so the discharges apply
    without massaging the statement. -/
example : Nat.Primrec (fun n => n.unpair.1) := Nat.Primrec.left

example : Nat.Primrec (fun n => n.unpair.2) := Nat.Primrec.right

/-- The `pair` constructor's function is built. -/
example (f g : Nat → Nat) (hf : Builds f) (hg : Builds g) :
    Builds (fun n => Nat.pair (f n) (g n)) :=
  builds_pair f g hf hg

/-- In the shape the inductive uses. -/
example (f g : Nat → Nat) (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => Nat.pair (f n) (g n)) :=
  Nat.Primrec.pair hf hg

/-- The primitive recursion body's prelude ends with the two clears that
    give the step function's fragment the conditions it requires. -/
example : (precBodyPre 2 0)[102]? = some (Instruction.jzdec 3 103 102) := rfl

example : (precBodyPre 2 0)[103]? = some (Instruction.jzdec 5 104 103) := rfl

example : (precBodyPre 2 0).length = 104 := rfl

/-- Its postlude clears the assembled argument, counts the iteration, and
    returns to the head by testing a register the invariant keeps empty. -/
example : precBodyPost 2 200 3 = [Instruction.jzdec 6 201 200,
    Instruction.inc 4 202, Instruction.jzdec 8 3 3] := rfl

/-- After the loop the counter holds the number of iterations, so the
    cleanup clears it as well as the argument. -/
example : precPost 1 2 300 9000 = [Instruction.jzdec 3 302 301,
    Instruction.inc 1 300, Instruction.jzdec 2 303 302,
    Instruction.jzdec 4 9000 303] := rfl

/-- The cases already discharged in `Theory.Universal.Builder`. -/
example : Builds (fun _ => 0) := builds_zero

example : Builds Nat.succ := builds_succ

example (f g : Nat → Nat) (hf : Builds f) (hg : Builds g) : Builds (fun n => f (g n)) :=
  builds_comp f g hf hg

end LeanBF.Tests
