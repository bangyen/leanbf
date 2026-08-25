/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Multiply

/-!
# Multiplication Tests

Kernel re-assertions of variable multiplication on a concrete program.

## Main definitions

* `mulVarProg`: A six-instruction multiplication fragment followed by `halt`.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- Multiply register `0` by register `1` into register `2`, using `3` as
    scratch, then halt. -/
def mulVarProg : Program :=
  [.jzdec 1 6 1, .jzdec 0 4 2, .inc 2 3, .inc 3 1, .jzdec 3 0 5, .inc 0 4, .halt]

/-- The slots sit where `mulVar_effect` requires. -/
example : mulVarProg[0]? = some (Instruction.jzdec 1 6 1) := rfl

example : mulVarProg[4]? = some (Instruction.jzdec 3 0 5) := rfl

/-- Three times four is twelve, with the multiplicand surviving. -/
example : ∃ s', Reaches mulVarProg
      { pc := 0, regs := fun i => if i = 0 then 3 else if i = 1 then 4 else 0 } s' ∧
    s'.pc = 6 ∧ s'.regs 1 = 0 ∧ s'.regs 0 = 3 ∧ s'.regs 3 = 0 ∧ s'.regs 2 = 12 := by
  rcases mulVar_effect mulVarProg 0 1 2 3 0 6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    { pc := 0, regs := fun i => if i = 0 then 3 else if i = 1 then 4 else 0 } rfl rfl with
    ⟨s', hr, hpc, hb, ha, hsc, ht, _⟩
  refine ⟨s', hr, hpc, hb, ?_, hsc, ?_⟩
  · rw [ha]
    rfl
  · rw [ht]
    rfl

/-- The invariant ignores the counter register, as `iterate_inv` demands. -/
example (a t sc a0 t0 b0 c : Nat) (hac : a ≠ c) (htc : t ≠ c) (hscc : sc ≠ c)
    (m : Nat) (f g : Nat → Nat) (h : ∀ i, i ≠ c → f i = g i)
    (hI : MulInv a t sc a0 t0 b0 m f) : MulInv a t sc a0 t0 b0 m g :=
  mulInv_congr a t sc a0 t0 b0 c hac htc hscc m f g h hI

end LeanBF.Tests
