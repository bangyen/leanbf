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

/-- The `prec` constructor's function is built, in the shape the inductive
    states it. -/
example (f g : Nat → Nat) (hf : Builds f) (hg : Builds g) :
    Builds (Nat.unpaired fun z n => n.rec (f z) fun y IH => g (Nat.pair z (Nat.pair y IH))) :=
  builds_prec f g hf hg

/-- Every primitive recursive function has a builder. -/
example {f : Nat → Nat} (hf : Nat.Primrec f) : Builds f := primrec_builds hf

/-- And so is computed by a register machine. -/
example {f : Nat → Nat} (hf : Nat.Primrec f) : RegComputable f := primrec_regComputable hf

/-- Concretely: addition of a constant is primitive recursive, so a register
    machine computes it. -/
example : RegComputable (fun n => n + 1) :=
  primrec_regComputable (Nat.Primrec.succ)

/-- And so is any constant function. -/
example (k : Nat) : RegComputable (fun _ => k) :=
  primrec_regComputable (Nat.Primrec.const k)

/-- The cases already discharged in `Theory.Universal.Builder`. -/
example : Builds (fun _ => 0) := builds_zero

example : Builds Nat.succ := builds_succ

example (f g : Nat → Nat) (hf : Builds f) (hg : Builds g) : Builds (fun n => f (g n)) :=
  builds_comp f g hf hg

end LeanBF.Tests
