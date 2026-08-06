/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics
import LeanBF.Theory.Semantics

/-!
# Semantics Tests

Kernel re-assertions of the `LeanBF.Core.Semantics` definitions and the
`LeanBF.Theory.Semantics` lemmas.
-/

namespace LeanBF.Tests

open LeanBF

example : step [] State.mkEmpty = none :=
  rfl

example : step [.inc_val] State.mkEmpty = some ([], State.incVal State.mkEmpty) :=
  rfl

example : step [.write] State.mkEmpty = some ([], { State.mkEmpty with output := [0] }) :=
  rfl

example : RunsTo ([], State.mkEmpty) State.mkEmpty :=
  RunsTo.halt State.mkEmpty

example : step [.inc_ptr] State.mkEmpty = some ([], State.incPtr State.mkEmpty) :=
  step_incPtr State.mkEmpty

example (s : State) (body : Program) (h : State.currentVal s = 0) :
    step [.loop body] s = some ([], s) :=
  step_loop_zero s body h

example (s : State) : halts [] s :=
  halts_empty s

end LeanBF.Tests
