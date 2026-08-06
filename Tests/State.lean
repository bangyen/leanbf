/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.State

/-!
# State Tests
-/

namespace LeanBF.Tests

open LeanBF

example : State.ptr State.mkEmpty = 0 :=
  rfl

example : State.input State.mkEmpty = [] :=
  rfl

example : State.output State.mkEmpty = [] :=
  rfl

example : State.currentVal State.mkEmpty = 0 :=
  rfl

example : State.incPtr State.mkEmpty = { State.mkEmpty with ptr := 1 } :=
  rfl

example : State.currentVal (State.incVal State.mkEmpty) = 1 :=
  rfl

end LeanBF.Tests
