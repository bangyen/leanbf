/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Pair

/-!
# Pairing Tests

Kernel re-assertions of the pairing fragment's layout and of what it
computes, on both sides of the comparison that selects its arm.

## Main definitions

* `pairProg`: The pairing fragment over registers `0` and `1`.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- Pair register `0` with register `1` into register `2`, working block at
    `3`, laid out from zero and exiting at `200`. -/
def pairProg : Program := pairFrag 0 1 2 3 0 200

/-- The fragment occupies fifty-one slots. -/
example : pairProg.length = 51 := pairFrag_length 0 1 2 3 0 200

/-- The comparison's two arms start where the fragment says they do. -/
example : pairProg[12]? = some (Instruction.jzdec 6 30 13) := rfl

example : pairProg[14]? = some (Instruction.jzdec 1 17 15) := rfl

example : pairProg[30]? = some (Instruction.jzdec 0 33 31) := rfl

/-- `Nat.pair` on both sides of the comparison, and on the diagonal where the
    two arguments are equal and the non-strict arm has to run. -/
example : Nat.pair 1 3 = 10 := rfl

example : Nat.pair 3 1 = 13 := rfl

example : Nat.pair 2 2 = 8 := rfl

/-- The fragment computes the pairing function, preserving both operands and
    leaving its working block clear. -/
example (p : Program) (a b out lo base exit : Nat)
    (hab : a ≠ b) (hao : a ≠ out) (hbo : b ≠ out)
    (ha : a < lo) (hb : b < lo) (ho : out < lo)
    (hemb : EmbeddedAt p base (pairFrag a b out lo base exit))
    (s : State) (hpc : s.pc = base) (hout : s.regs out = 0)
    (hz : ∀ j, j < 8 → s.regs (lo + j) = 0) :
    ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs a = s.regs a ∧
      s'.regs b = s.regs b ∧ s'.regs out = Nat.pair (s.regs a) (s.regs b) ∧
      (∀ j, j < 8 → s'.regs (lo + j) = 0) ∧
      ∀ q, q ≠ a → q ≠ b → q ≠ out → (q < lo ∨ lo + 8 ≤ q) → s'.regs q = s.regs q :=
  pairVar_effect p a b out lo base exit hab hao hbo ha hb ho hemb s hpc hout hz

end LeanBF.Tests
