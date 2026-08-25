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

* `jzdecHead`: The block's pieces before the restore arms.
* `jzdecArms`: The restore arms, laid end to end.
* `jzdecBlock`: The block that tests and decrements a packed register.

## Theorems

* `jzdecHead_length`: The head's length.
* `jzdecArms_length`: The arms' total length.
* `jzdecBlockLen`: The block's length.
* `jzdecBlock_get_head`: A low slot is read from the head.
* `jzdecHead_get_entry`: The block's entry no-op.
* `jzdecHead_get_div`: The divide loop's test chain.
* `jzdecHead_get_divInc`: The divide loop's increment.
* `jzdecHead_get_table`: The jump table.
* `jzdecHead_get_drain0`: The drain's test.
* `jzdecHead_get_drain1`: The drain's increment.
-/

namespace LeanBF

namespace Register

/-- Where a remainder's handler begins: the drain for zero, and otherwise the
    arm for that remainder, the arms being uniformly `2 * p` long. -/
def jzdecDest (p base r : Nat) : Nat :=
  if r = 0 then base + 2 + 2 * p else base + 2 + 2 * p + 2 + (r - 1) * (2 * p)

/-- Everything before the restore arms: the entry no-op, the divide loop,
    the jump table, and the drain. Naming it lets a slot lookup split the
    block once rather than peeling four appends. -/
def jzdecHead (p base ifNonZero : Nat) : Program :=
  Instruction.jzdec 1 (base + 1) (base + 1)
  :: ((List.range p).map (fun j =>
        Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))
      ++ Instruction.inc 1 (base + 1)
        :: ((List.range p).map (fun r =>
              Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))
            ++ [Instruction.jzdec 1 ifNonZero (base + 2 + 2 * p + 1),
                Instruction.inc 0 (base + 2 + 2 * p)]))

theorem jzdecHead_length (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero).length = 2 + 2 * p + 2 := by
  simp only [jzdecHead, List.length_cons, List.length_append, List.length_map,
    List.length_range, List.length_nil]
  omega

/-- The arms, laid end to end, each padded to the same length. -/
def jzdecArms (p base ifZero : Nat) : Program :=
  (List.range (p - 1)).flatMap (fun i =>
    paddedArm p (i + 1) (base + 2 + 2 * p + 2 + i * (2 * p)) ifZero)

theorem jzdecArms_length (p base ifZero : Nat) :
    (jzdecArms p base ifZero).length = (p - 1) * (2 * p) := by
  rw [jzdecArms, List.length_flatMap]
  have hconst : ∀ i ∈ List.range (p - 1),
      (paddedArm p (i + 1) (base + 2 + 2 * p + 2 + i * (2 * p)) ifZero).length = 2 * p := by
    intro i hi
    exact paddedArm_length p (i + 1) _ _ (by have := List.mem_range.mp hi; omega)
  rw [List.map_congr_left hconst, List.map_const', List.sum_replicate_nat,
    List.length_range]

/-- The block that tests and decrements a packed register. -/
def jzdecBlock (p base ifZero ifNonZero : Nat) : Program :=
  jzdecHead p base ifNonZero ++ jzdecArms p base ifZero

theorem jzdecBlockLen (p base ifZero ifNonZero : Nat) :
    (jzdecBlock p base ifZero ifNonZero).length = 2 + 2 * p + 2 + (p - 1) * (2 * p) := by
  rw [jzdecBlock, List.length_append, jzdecHead_length, jzdecArms_length]

/-- Reading the block's slots. Everything below `2 + 2 * p + 2` lives in the
    head, so one split sends the lookup to the right piece. -/
theorem jzdecBlock_get_head (p base ifZero ifNonZero j : Nat) (hj : j < 2 + 2 * p + 2) :
    (jzdecBlock p base ifZero ifNonZero)[j]? = (jzdecHead p base ifNonZero)[j]? := by
  rw [jzdecBlock, List.getElem?_append_left (by rw [jzdecHead_length]; exact hj)]

theorem jzdecHead_get_entry (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[0]? =
      some (Instruction.jzdec 1 (base + 1) (base + 1)) := rfl

theorem jzdecHead_get_div (p base ifNonZero j : Nat) (hj : j < p) :
    (jzdecHead p base ifNonZero)[1 + j]? =
      some (Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 1 + j = j + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by rw [hlen]; exact hj), List.getElem?_map,
    List.getElem?_range hj]
  rfl

theorem jzdecHead_get_divInc (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[1 + p]? = some (Instruction.inc 1 (base + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 1 + p = p + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

theorem jzdecHead_get_table (p base ifNonZero r : Nat) (hr : r < p) :
    (jzdecHead p base ifNonZero)[2 + p + r]? =
      some (Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  have hlen2 : ((List.range p).map (fun r =>
      Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 2 + p + r = (p + r + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show p + r + 1 - p = r + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by rw [hlen2]; exact hr), List.getElem?_map,
    List.getElem?_range hr]
  rfl

theorem jzdecHead_get_drain0 (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[2 + 2 * p]? =
      some (Instruction.jzdec 1 ifNonZero (base + 2 + 2 * p + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  have hlen2 : ((List.range p).map (fun r =>
      Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 2 + 2 * p = (2 * p + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show 2 * p + 1 - p = p + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen2]), hlen2, Nat.sub_self]
  rfl

theorem jzdecHead_get_drain1 (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[2 + 2 * p + 1]? =
      some (Instruction.inc 0 (base + 2 + 2 * p)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  have hlen2 : ((List.range p).map (fun r =>
      Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 2 + 2 * p + 1 = (2 * p + 2) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show 2 * p + 2 - p = p + 2 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen2]; omega), hlen2,
    show p + 1 - p = 1 by omega]
  rfl

end Register

end LeanBF
