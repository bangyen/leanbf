/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Completeness

/-!
# Completeness Tests

Kernel re-assertions of the `Simulates` relation on concrete states.
-/

namespace LeanBF.Tests

open LeanBF

example : Simulates { pc := 1, c1 := 2, c2 := 3 }
    { ptr := 0,
      tape := fun i => if i = 0 then 1 else if i = 1 then 1 else if i = 2 then 2 else 3,
      input := [], output := [] } := by
  unfold Simulates
  decide

example : ¬ Simulates { pc := 0, c1 := 0, c2 := 0 } State.mkEmpty := by
  unfold Simulates
  decide

end LeanBF.Tests
