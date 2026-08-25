/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Unpair

/-!
# Unpairing Tests

Kernel re-assertions of the unpairing fragment's layout and of the arithmetic
it implements, on both sides of the comparison that selects its arm.

## Main definitions

* `unpairProg`: The unpairing fragment over register `0`.

## Theorems

* `sqrt_five`: The square root of five is two.
* `sqrt_seven`: The square root of seven is two.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- Unpair register `0` into registers `1` and `2`, working registers from
    `3`, laid out from zero and exiting at `500`. -/
def unpairProg : Program := unpairFrag 0 1 2 3 0 500

/-- The fragment occupies ninety-three slots. -/
example : unpairProg.length = 93 := unpairFrag_length 0 1 2 3 0 500

/-- The square-root search's loop head and the comparison that follows the
    subtraction sit where the layout says. -/
example : unpairProg[5]? = some (Instruction.jzdec 12 40 6) := rfl

example : unpairProg[76]? = some (Instruction.jzdec 16 82 77) := rfl

/-- The roots the two cases below turn on, from the defining
    characterization rather than by evaluation. -/
theorem sqrt_five : Nat.sqrt 5 = 2 := by
  have hlo : 2 ≤ Nat.sqrt 5 := Nat.le_sqrt.mpr (by omega)
  have hhi : ¬ (3 ≤ Nat.sqrt 5) := fun h => by
    have := Nat.le_sqrt.mp h
    omega
  omega

theorem sqrt_seven : Nat.sqrt 7 = 2 := by
  have hlo : 2 ≤ Nat.sqrt 7 := Nat.le_sqrt.mpr (by omega)
  have hhi : ¬ (3 ≤ Nat.sqrt 7) := fun h => by
    have := Nat.le_sqrt.mp h
    omega
  omega

/-- Unpairing takes the first arm when the remainder is below the root. -/
example : Nat.unpair 5 = (1, 2) := by
  simp only [Nat.unpair, sqrt_five]
  norm_num

/-- And the second when it is not, which is where the root becomes the first
    answer rather than the second. -/
example : Nat.unpair 7 = (2, 1) := by
  simp only [Nat.unpair, sqrt_seven]
  norm_num

/-- The fragment computes both halves of the unpairing, preserving its input
    and leaving its working block clear. -/
example (p : Program) (nR o1 o2 lo base exit : Nat)
    (hn1 : nR ≠ o1) (hn2 : nR ≠ o2) (h12 : o1 ≠ o2)
    (hnl : nR < lo) (h1l : o1 < lo) (h2l : o2 < lo)
    (hemb : EmbeddedAt p base (unpairFrag nR o1 o2 lo base exit))
    (s : State) (hpc : s.pc = base) (ho1 : s.regs o1 = 0) (ho2 : s.regs o2 = 0)
    (hz : ∀ j, j < 16 → s.regs (lo + j) = 0) :
    ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs nR = s.regs nR ∧
      s'.regs o1 = (Nat.unpair (s.regs nR)).1 ∧
      s'.regs o2 = (Nat.unpair (s.regs nR)).2 ∧
      (∀ j, j < 16 → s'.regs (lo + j) = 0) ∧
      ∀ q, q ≠ nR → q ≠ o1 → q ≠ o2 → (q < lo ∨ lo + 16 ≤ q) → s'.regs q = s.regs q :=
  unpairVar_effect p nR o1 o2 lo base exit hn1 hn2 h12 hnl h1l h2l hemb s hpc ho1 ho2 hz

/-- Unpairing inverts pairing, which is what the two together are for. -/
example : Nat.unpair (Nat.pair 3 4) = (3, 4) := by
  rw [Nat.unpair_pair]

end LeanBF.Tests
