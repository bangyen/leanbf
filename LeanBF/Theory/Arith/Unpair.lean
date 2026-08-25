/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Pair

/-!
# The Unpairing Function

`Nat.unpair n` takes `s` to be `Nat.sqrt n` and `d` to be `n - s * s`, then
answers `(d, s)` when `d < s` and `(s, d - s)` otherwise. The fragment
therefore runs the square-root search, squares its answer back, subtracts to
recover `d`, and compares.

It is the largest single fragment here, and the only one with two outputs.
Two outputs are what the induction actually needs: `left` and `right` are the
two halves of one computation, and building them separately would run the
square-root search twice.

The comparison's arms are where the two answers are assembled. Both drain
rather than copy, since nothing after them reads `s` or `d` again.

## Main definitions

* `unpairRestFrag`: The stages that follow the square-root search.
* `unpairFrag`: The unpairing function as a concrete instruction list.

## Theorems

* `unpairFrag_length`: The fragment occupies ninety-three slots.
-/

namespace LeanBF

namespace Register

/-- The stages after the square root: squaring the root back,
    recovering the remainder, and the comparison whose arms assemble the two
    answers. Laid out from its own base, which is forty slots past the
    fragment's. -/
def unpairRestFrag (nR o1 o2 lo base exit : Nat) : Program :=
  [.jzdec lo (base + 3) (base + 1),
   .inc (lo + 11) (base + 2),
   .inc (lo + 12) base,
   .jzdec (lo + 12) (base + 5) (base + 4),
   .inc lo (base + 3),
   .jzdec (lo + 11) (base + 11) (base + 6),
   .jzdec lo (base + 9) (base + 7),
   .inc (lo + 10) (base + 8),
   .inc (lo + 12) (base + 6),
   .jzdec (lo + 12) (base + 5) (base + 10),
   .inc lo (base + 9),
   .jzdec nR (base + 14) (base + 12),
   .inc (lo + 1) (base + 13),
   .inc (lo + 12) (base + 11),
   .jzdec (lo + 12) (base + 16) (base + 15),
   .inc nR (base + 14),
   .jzdec (lo + 10) (base + 19) (base + 17),
   .inc (lo + 14) (base + 18),
   .inc (lo + 12) (base + 16),
   .jzdec (lo + 12) (base + 21) (base + 20),
   .inc (lo + 10) (base + 19),
   .jzdec (lo + 14) (base + 23) (base + 22),
   .jzdec (lo + 1) (base + 21) (base + 21),
   .jzdec (lo + 10) (base + 24) (base + 23),
   .jzdec lo (base + 27) (base + 25),
   .inc (lo + 13) (base + 26),
   .inc (lo + 15) (base + 24),
   .jzdec (lo + 15) (base + 29) (base + 28),
   .inc lo (base + 27),
   .jzdec (lo + 1) (base + 32) (base + 30),
   .inc (lo + 14) (base + 31),
   .inc (lo + 15) (base + 29),
   .jzdec (lo + 15) (base + 34) (base + 33),
   .inc (lo + 1) (base + 32),
   .jzdec (lo + 14) (base + 36) (base + 35),
   .jzdec (lo + 13) (base + 34) (base + 34),
   .jzdec (lo + 13) (base + 42) (base + 37),
   .jzdec (lo + 13) (base + 38) (base + 37),
   .jzdec (lo + 1) (base + 40) (base + 39),
   .inc o1 (base + 38),
   .jzdec lo exit (base + 41),
   .inc o2 (base + 40),
   .jzdec lo (base + 45) (base + 43),
   .inc (lo + 14) (base + 44),
   .inc (lo + 15) (base + 42),
   .jzdec (lo + 15) (base + 47) (base + 46),
   .inc lo (base + 45),
   .jzdec (lo + 14) (base + 49) (base + 48),
   .jzdec (lo + 1) (base + 47) (base + 47),
   .jzdec lo (base + 51) (base + 50),
   .inc o1 (base + 49),
   .jzdec (lo + 1) exit (base + 52),
   .inc o2 (base + 51)]

/-- The unpairing function. Slots `0` to `39` are the square-root search,
    `40` to `50` square its answer back, `51` to `63` recover the remainder
    and clear the square, and `64` onward compare the remainder against the
    root and assemble the two answers.

    The named registers are the input and the two outputs; `lo` holds the
    root and `lo + 1` the remainder, with the search's own working block at
    `lo + 2` through `lo + 9` and the rest above it.

    Stating this as a concatenation rather than one flat list is what lets
    the search be cited as a lemma instead of re-proved slot by slot. -/
def unpairFrag (nR o1 o2 lo base exit : Nat) : Program :=
  sqrtFrag nR lo (lo + 2) base (base + 40) ++
    unpairRestFrag nR o1 o2 lo (base + 40) exit

theorem unpairFrag_length (nR o1 o2 lo base exit : Nat) :
    (unpairFrag nR o1 o2 lo base exit).length = 93 := rfl

end Register

end LeanBF
