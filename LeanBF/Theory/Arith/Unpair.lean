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

* `unpairFrag`: The unpairing function as a concrete instruction list.

## Theorems

* `unpairFrag_length`: The fragment occupies ninety-three slots.
-/

namespace LeanBF

namespace Register

/-- The unpairing function, laid out from `base`. Slots `0` to `39` are the
    square-root search, `40` to `50` square its answer back, `51` to `63`
    recover the remainder and clear the square, and `64` onward compare the
    remainder against the root and assemble the two answers.

    The named registers are the input and the two outputs; `lo` holds the
    root and `lo + 1` the remainder, with the search's own working block at
    `lo + 2` through `lo + 9` and the rest of the working registers above
    it. -/
def unpairFrag (nR o1 o2 lo base exit : Nat) : Program :=
  [.jzdec nR (base + 3) (base + 1),
   .inc (lo + 9) (base + 2),
   .inc (lo + 2) base,
   .jzdec (lo + 2) (base + 5) (base + 4),
   .inc nR (base + 3),
   .jzdec (lo + 9) (base + 40) (base + 6),
   .jzdec lo (base + 9) (base + 7),
   .inc (lo + 2) (base + 8),
   .inc (lo + 7) (base + 6),
   .jzdec (lo + 7) (base + 11) (base + 10),
   .inc lo (base + 9),
   .inc (lo + 2) (base + 12),
   .jzdec (lo + 2) (base + 15) (base + 13),
   .inc (lo + 4) (base + 14),
   .inc (lo + 7) (base + 12),
   .jzdec (lo + 7) (base + 17) (base + 16),
   .inc (lo + 2) (base + 15),
   .jzdec (lo + 4) (base + 23) (base + 18),
   .jzdec (lo + 2) (base + 21) (base + 19),
   .inc (lo + 3) (base + 20),
   .inc (lo + 7) (base + 18),
   .jzdec (lo + 7) (base + 17) (base + 22),
   .inc (lo + 2) (base + 21),
   .jzdec (lo + 3) (base + 26) (base + 24),
   .inc (lo + 5) (base + 25),
   .inc (lo + 8) (base + 23),
   .jzdec (lo + 8) (base + 28) (base + 27),
   .inc (lo + 3) (base + 26),
   .jzdec nR (base + 31) (base + 29),
   .inc (lo + 6) (base + 30),
   .inc (lo + 8) (base + 28),
   .jzdec (lo + 8) (base + 33) (base + 32),
   .inc nR (base + 31),
   .jzdec (lo + 6) (base + 35) (base + 34),
   .jzdec (lo + 5) (base + 33) (base + 33),
   .jzdec (lo + 5) (base + 37) (base + 36),
   .jzdec (lo + 5) (base + 38) (base + 36),
   .inc lo (base + 38),
   .jzdec (lo + 2) (base + 39) (base + 38),
   .jzdec (lo + 3) (base + 5) (base + 39),
   .jzdec lo (base + 43) (base + 41),
   .inc (lo + 11) (base + 42),
   .inc (lo + 12) (base + 40),
   .jzdec (lo + 12) (base + 45) (base + 44),
   .inc lo (base + 43),
   .jzdec (lo + 11) (base + 51) (base + 46),
   .jzdec lo (base + 49) (base + 47),
   .inc (lo + 10) (base + 48),
   .inc (lo + 12) (base + 46),
   .jzdec (lo + 12) (base + 45) (base + 50),
   .inc lo (base + 49),
   .jzdec nR (base + 54) (base + 52),
   .inc (lo + 1) (base + 53),
   .inc (lo + 12) (base + 51),
   .jzdec (lo + 12) (base + 56) (base + 55),
   .inc nR (base + 54),
   .jzdec (lo + 10) (base + 59) (base + 57),
   .inc (lo + 14) (base + 58),
   .inc (lo + 12) (base + 56),
   .jzdec (lo + 12) (base + 61) (base + 60),
   .inc (lo + 10) (base + 59),
   .jzdec (lo + 14) (base + 63) (base + 62),
   .jzdec (lo + 1) (base + 61) (base + 61),
   .jzdec (lo + 10) (base + 64) (base + 63),
   .jzdec lo (base + 67) (base + 65),
   .inc (lo + 13) (base + 66),
   .inc (lo + 15) (base + 64),
   .jzdec (lo + 15) (base + 69) (base + 68),
   .inc lo (base + 67),
   .jzdec (lo + 1) (base + 72) (base + 70),
   .inc (lo + 14) (base + 71),
   .inc (lo + 15) (base + 69),
   .jzdec (lo + 15) (base + 74) (base + 73),
   .inc (lo + 1) (base + 72),
   .jzdec (lo + 14) (base + 76) (base + 75),
   .jzdec (lo + 13) (base + 74) (base + 74),
   .jzdec (lo + 13) (base + 82) (base + 77),
   .jzdec (lo + 13) (base + 78) (base + 77),
   .jzdec (lo + 1) (base + 80) (base + 79),
   .inc o1 (base + 78),
   .jzdec lo exit (base + 81),
   .inc o2 (base + 80),
   .jzdec lo (base + 85) (base + 83),
   .inc (lo + 14) (base + 84),
   .inc (lo + 15) (base + 82),
   .jzdec (lo + 15) (base + 87) (base + 86),
   .inc lo (base + 85),
   .jzdec (lo + 14) (base + 89) (base + 88),
   .jzdec (lo + 1) (base + 87) (base + 87),
   .jzdec lo (base + 91) (base + 90),
   .inc o1 (base + 89),
   .jzdec (lo + 1) exit (base + 92),
   .inc o2 (base + 91)]

theorem unpairFrag_length (nR o1 o2 lo base exit : Nat) :
    (unpairFrag nR o1 o2 lo base exit).length = 93 := rfl

end Register

end LeanBF
