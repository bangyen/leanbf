/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Subtract

/-!
# Subtraction and Comparison Tests

Kernel re-assertions of truncated subtraction and of the comparison that
answers by which address it exits from, including the boundary case where the
two registers are equal.

## Main definitions

* `cmpProg`: A comparison fragment over registers `0` and `1`.
* `cmpStart`: The comparison fragment's starting state, given two operands.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- Compare register `0` against register `1`, using `2`, `3` and `4` as
    working registers. Exits at `14` when `0 < 1` and at `15` otherwise. -/
def cmpProg : Program :=
  [.jzdec 1 3 1, .inc 2 2, .inc 4 0,
   .jzdec 4 5 4, .inc 1 3,
   .jzdec 0 8 6, .inc 3 7, .inc 4 5,
   .jzdec 4 10 9, .inc 0 8,
   .jzdec 3 12 11, .jzdec 2 10 10,
   .jzdec 2 15 13, .jzdec 2 14 13,
   .halt, .halt]

/-- The starting state for a comparison of `x` against `y`. -/
def cmpStart (x y : Nat) : State :=
  { pc := 0, regs := fun i => if i = 0 then x else if i = 1 then y else 0 }

/-- The comparison exits at `14` when the first operand is strictly less. -/
example : ∃ s', Reaches cmpProg (cmpStart 2 5) s' ∧ s'.pc = 14 := by
  rcases cmpBranch_effect cmpProg 0 1 2 3 4 0 3 5 8 10 12 13 14 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (cmpStart 2 5) rfl rfl rfl rfl with ⟨s', hr, _, _, _, _, _, hpc⟩
  exact ⟨s', hr, by rw [hpc]; decide⟩

/-- It exits at `15` when the first operand is strictly greater. -/
example : ∃ s', Reaches cmpProg (cmpStart 5 2) s' ∧ s'.pc = 15 := by
  rcases cmpBranch_effect cmpProg 0 1 2 3 4 0 3 5 8 10 12 13 14 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (cmpStart 5 2) rfl rfl rfl rfl with ⟨s', hr, _, _, _, _, _, hpc⟩
  exact ⟨s', hr, by rw [hpc]; decide⟩

/-- Equal operands take the `15` arm, since the comparison is strict. This
    is the boundary the two-armed constructions above depend on. -/
example : ∃ s', Reaches cmpProg (cmpStart 3 3) s' ∧ s'.pc = 15 := by
  rcases cmpBranch_effect cmpProg 0 1 2 3 4 0 3 5 8 10 12 13 14 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (cmpStart 3 3) rfl rfl rfl rfl with ⟨s', hr, _, _, _, _, _, hpc⟩
  exact ⟨s', hr, by rw [hpc]; decide⟩

/-- Both operands survive the comparison, and every working register is
    left clear on whichever arm was taken. -/
example : ∃ s', Reaches cmpProg (cmpStart 2 5) s' ∧ s'.regs 0 = 2 ∧
    s'.regs 1 = 5 ∧ s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 := by
  rcases cmpBranch_effect cmpProg 0 1 2 3 4 0 3 5 8 10 12 13 14 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (cmpStart 2 5) rfl rfl rfl rfl with ⟨s', hr, ha, hb, hsc, hc, ht, _⟩
  exact ⟨s', hr, by rw [ha]; rfl, by rw [hb]; rfl, ht, hc, hsc⟩

/-- The subtraction loop saturates rather than underflowing. -/
example (p : Program) (t c base exit : Nat) (htc : t ≠ c)
    (hloop : p[base]? = some (Instruction.jzdec c exit (base + 1)))
    (hbody : p[base + 1]? = some (Instruction.jzdec t base base))
    (s : State) (hpc : s.pc = base) :
    ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs c = 0 ∧
      s'.regs t = s.regs t - s.regs c ∧ ∀ r, r ≠ t → r ≠ c → s'.regs r = s.regs r :=
  subLoop_effect p t c base exit htc hloop hbody s hpc

end LeanBF.Tests
