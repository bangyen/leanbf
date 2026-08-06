/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Minsky

/-!
# Minsky Tests
-/

namespace LeanBF.Tests

open LeanBF

example : Minsky.step [] { pc := 0, c1 := 0, c2 := 0 } = none :=
  rfl

example : Minsky.step [.halt] { pc := 0, c1 := 0, c2 := 0 } = none :=
  rfl

example : Minsky.step [.inc1 1] { pc := 0, c1 := 0, c2 := 0 } =
    some { pc := 1, c1 := 1, c2 := 0 } :=
  rfl

example : Minsky.step [.jzdec1 0 1] { pc := 0, c1 := 2, c2 := 0 } =
    some { pc := 1, c1 := 1, c2 := 0 } :=
  rfl

example : Minsky.step [.jzdec2 0 1] { pc := 0, c1 := 0, c2 := 2 } =
    some { pc := 1, c1 := 0, c2 := 1 } :=
  rfl

end LeanBF.Tests
