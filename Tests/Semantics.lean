/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics

/-!
# Semantics Tests
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

end LeanBF.Tests
