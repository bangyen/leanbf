/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing.Blocks

/-!
# The Conditional Block

What a `jzdec` becomes once the register file is a single number.

Testing a packed register and decrementing it are the same operation. The
register is non-zero exactly when its prime divides the packed value, and the
decrement is that division — so one divide loop answers the test and performs
the update at once, branching by which remainder it exits on. That is the
same economy the search tail found, where a single `jzdec` both detected
success and decoded it.

The layout has four parts after the entry no-op:

* the divide loop, whose `p` exits are contiguous by construction;
* a jump table of `p` slots, one per remainder, each an unconditional jump —
  the divide leaves the packed counter empty, so a test of it always takes
  the zero branch, which is how a machine with no plain jump makes one;
* the drain, taken on remainder zero, which pours the quotient back and
  leaves for `ifNonZero`;
* the restore arms, one per non-zero remainder, each padded to `2 * p` so its
  address is a closed form rather than a sum over the arms before it.

The jump table exists because `div_reaches` puts its exits at consecutive
addresses, while the destinations they stand for are spread out. Rather than
weaken that lemma, the table absorbs the difference in one slot each.

## Main definitions

* `jzdecBlock`: The block that tests and decrements a packed register.

## Theorems

* `jzdecBlockLen`: Its length.
-/

namespace LeanBF

namespace Register

/-- Where a remainder's handler begins: the drain for zero, and otherwise the
    arm for that remainder, the arms being uniformly `2 * p` long. -/
def jzdecDest (p base r : Nat) : Nat :=
  if r = 0 then base + 2 + 2 * p else base + 2 + 2 * p + 2 + (r - 1) * (2 * p)

/-- The block that tests and decrements a packed register. -/
def jzdecBlock (p base ifZero ifNonZero : Nat) : Program :=
  [Instruction.jzdec 1 (base + 1) (base + 1)]
  ++ (List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))
  ++ [Instruction.inc 1 (base + 1)]
  ++ (List.range p).map (fun r =>
      Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))
  ++ [Instruction.jzdec 1 ifNonZero (base + 2 + 2 * p + 1),
      Instruction.inc 0 (base + 2 + 2 * p)]
  ++ (List.range (p - 1)).flatMap (fun i =>
      paddedArm p (i + 1) (base + 2 + 2 * p + 2 + i * (2 * p)) ifZero)

theorem jzdecBlockLen (p base ifZero ifNonZero : Nat) (hp : 0 < p) :
    (jzdecBlock p base ifZero ifNonZero).length = 2 + 2 * p + 2 + (p - 1) * (2 * p) := by
  have harms : ((List.range (p - 1)).flatMap (fun i =>
      paddedArm p (i + 1) (base + 2 + 2 * p + 2 + i * (2 * p)) ifZero)).length
      = (p - 1) * (2 * p) := by
    rw [List.length_flatMap]
    have hconst : ∀ i ∈ List.range (p - 1),
        (paddedArm p (i + 1) (base + 2 + 2 * p + 2 + i * (2 * p)) ifZero).length = 2 * p := by
      intro i hi
      exact paddedArm_length p (i + 1) _ _ (by
        have := List.mem_range.mp hi
        omega)
    rw [List.map_congr_left hconst, List.map_const', List.sum_replicate_nat,
      List.length_range]
  simp only [jzdecBlock, List.length_append, List.length_cons, List.length_map,
    List.length_range, List.length_nil, harms]
  omega

end Register

end LeanBF
