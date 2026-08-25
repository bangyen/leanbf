/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing.Divide

/-!
# Two-Counter Block Tests

Kernel re-assertions of the shapes an instruction compiles to. The block
lengths are computed at concrete primes, which is what a layout table's
arithmetic depends on.
-/

namespace LeanBF.Tests

open LeanBF LeanBF.Register

/-- An increment block is the register's prime plus four: an entry no-op, a
    scaled transfer of `p + 1` slots, and a two-slot drain. -/
example : (incBlock 2 0 100).length = 6 := by rw [incBlockLen]

example : (incBlock 7 0 100).length = 11 := by rw [incBlockLen]

/-- Its first slot is the entry no-op, which is what makes the block's run
    provably non-empty even when it exits to its own base. -/
example : (incBlock 3 0 100)[0]? = some (Instruction.jzdec 1 1 1) :=
  incBlock_get_entry 3 0 100

/-- A restore arm carries the multiply-back chain and one literal unit per
    remainder, and pads to a uniform width so its address is a closed form. -/
example : (restoreArm 5 3 0 100).length = 9 := by rw [restoreArm_length]

example : (paddedArm 5 3 0 100).length = 10 := paddedArm_length 5 3 0 100 (by omega)

/-- A conditional block grows with the square of the register's prime, the
    restore arms being one per non-zero remainder. -/
example : (jzdecBlock 2 0 100 200).length = 12 := by rw [jzdecBlockLen]

example : (jzdecBlock 3 0 100 200).length = 22 := by rw [jzdecBlockLen]

example : (jzdecBlock 5 0 100 200).length = 54 := by rw [jzdecBlockLen]

/-- Remainder zero is handled by the drain, just past the jump table. -/
example : jzdecDest 3 0 0 = 8 := by simp only [jzdecDest, if_pos trivial]

/-- Non-zero remainders select arms at uniform strides. -/
example : jzdecDest 3 0 1 = 10 := by
  simp only [jzdecDest, if_neg (by omega : ¬ (1 : Nat) = 0)]

example : jzdecDest 3 0 2 = 16 := by
  simp only [jzdecDest, if_neg (by omega : ¬ (2 : Nat) = 0)]

/-- Every block names only the two counters, which is the packing layer's
    central claim. -/
example (p base exit : Nat) :
    ∀ i ∈ incBlock p base exit, instrMentionsBelow 2 i := incBlock_mentions p base exit

example (p base z nz : Nat) :
    ∀ i ∈ jzdecBlock p base z nz, instrMentionsBelow 2 i := jzdecBlock_mentions p base z nz

end LeanBF.Tests
