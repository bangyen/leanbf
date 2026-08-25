/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Sqrt

/-!
# Square Root Tests

Kernel re-assertions of the search step's arithmetic and of the fragment
layout, including the perfect-square boundaries where an off-by-one in the
comparison would show.

## Main definitions

* `sqrtProg`: The search fragment over registers `0` and `1`.

## Theorems

* `sqrt_four`: The square root of four is two.
* `sqrt_three`: The square root of three is one.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- `Nat.sqrt` at the two boundary inputs, from its defining
    characterization rather than by evaluation. -/
theorem sqrt_four : Nat.sqrt 4 = 2 := by
  have hlo : 2 ≤ Nat.sqrt 4 := Nat.le_sqrt.mpr (by omega)
  have hhi : ¬ (3 ≤ Nat.sqrt 4) := fun h => by
    have := Nat.le_sqrt.mp h
    omega
  omega

theorem sqrt_three : Nat.sqrt 3 = 1 := by
  have hlo : 1 ≤ Nat.sqrt 3 := Nat.le_sqrt.mpr (by omega)
  have hhi : ¬ (2 ≤ Nat.sqrt 3) := fun h => by
    have := Nat.le_sqrt.mp h
    omega
  omega

/-- At four the candidate `2` still fits, so the answer advances to it. -/
example : (if (1 + 1) * (1 + 1) ≤ 4 then 1 + 1 else 1) = min (Nat.sqrt 4) (4 - 2) :=
  sqrtStep 4 2 1 (by omega) (by rw [sqrt_four]; omega)

/-- At three that same candidate overshoots, so the answer stays at one.
    These two are the perfect-square boundary the comparison decides: the
    candidate and the input differ by one, and only the strictness of the
    test separates them. -/
example : (if (1 + 1) * (1 + 1) ≤ 3 then 1 + 1 else 1) = min (Nat.sqrt 3) (3 - 1) :=
  sqrtStep 3 1 1 (by omega) (by rw [sqrt_three]; omega)

/-- The search fragment over registers `0` and `1`, with its working block
    at `2`, laid out from address `0` and exiting at `100`. -/
def sqrtProg : Program := sqrtBodyFrag 0 1 2 0 100

/-- The fragment occupies thirty-five slots. -/
example : sqrtProg.length = 35 := rfl

/-- Its loop head tests the counter at the top of the working block. -/
example : sqrtProg[0]? = some (Instruction.jzdec 9 100 1) := rfl

/-- The arm that advances the candidate increments register `1`. -/
example : sqrtProg[32]? = some (Instruction.inc 1 33) := rfl

/-- The two clears at the end empty the candidate copy and its square. -/
example : sqrtProg[33]? = some (Instruction.jzdec 2 34 33) := rfl

example : sqrtProg[34]? = some (Instruction.jzdec 3 0 34) := rfl

/-- A fragment embeds itself at base zero. -/
example : EmbeddedAt sqrtProg 0 (sqrtBodyFrag 0 1 2 0 100) := by
  intro j hj
  simp only [sqrtProg, Nat.zero_add]

/-- The prologue that loads the counter sits ahead of the loop head. -/
example : (sqrtFrag 0 1 2 0 100)[0]? = some (Instruction.jzdec 0 3 1) := rfl

example : (sqrtFrag 0 1 2 0 100)[5]? = some (Instruction.jzdec 9 100 6) := rfl

/-- The whole search: prologue plus loop. -/
example : (sqrtFrag 0 1 2 0 100).length = 40 := rfl

/-- The search computes the integer square root, preserving its input and
    leaving every working register clear. -/
example (p : Program) (nR r lo base exit : Nat)
    (hnr : nR ≠ r) (hn : nR < lo) (hr : r < lo)
    (hemb : EmbeddedAt p base (sqrtFrag nR r lo base exit))
    (s : State) (hpc : s.pc = base) (hr0 : s.regs r = 0)
    (hz : ∀ j, j < 8 → s.regs (lo + j) = 0) :
    ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs nR = s.regs nR ∧
      s'.regs r = Nat.sqrt (s.regs nR) ∧
      (∀ j, j < 8 → s'.regs (lo + j) = 0) ∧
      ∀ q, q ≠ nR → q ≠ r → (q < lo ∨ lo + 8 ≤ q) → s'.regs q = s.regs q :=
  sqrtVar_effect p nR r lo base exit hnr hn hr hemb s hpc hr0 hz

/-- One iteration of the search, as the loop above it uses it. -/
example (p : Program) (nR r lo base exit : Nat)
    (hnr : nR ≠ r) (hn : nR < lo) (hr : r < lo)
    (hemb : EmbeddedAt p base (sqrtBodyFrag nR r lo base exit))
    (n0 m : Nat) (s : State) (hpc : s.pc = base + 1) (hcnt : s.regs (lo + 7) = m)
    (hnv : s.regs nR = n0) (hrv : s.regs r = min (Nat.sqrt n0) (n0 - (m + 1)))
    (hz : ∀ j, j < 7 → s.regs (lo + j) = 0) (hmn : m + 1 ≤ n0) :
    ∃ s', Reaches p s s' ∧ s'.pc = base ∧ s'.regs (lo + 7) = m ∧
      s'.regs nR = n0 ∧ s'.regs r = min (Nat.sqrt n0) (n0 - m) ∧
      (∀ j, j < 7 → s'.regs (lo + j) = 0) ∧
      ∀ q, q ≠ nR → q ≠ r → (q < lo ∨ lo + 8 ≤ q) → s'.regs q = s.regs q :=
  sqrtBody_effect p nR r lo base exit hnr hn hr hemb n0 m s hpc hcnt hnv hrv hz hmn

end LeanBF.Tests
