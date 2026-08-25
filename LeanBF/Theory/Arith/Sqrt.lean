/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Multiply
import LeanBF.Theory.Arith.Subtract
import LeanBF.Theory.Universal.Builder

/-!
# Squaring and Integer Square Root

Squaring a register, and the upward search that inverts it.

`Nat.sqrt` is the largest `r` with `r * r ≤ n`, which a machine finds by
testing `1, 2, 3, …` in turn and stopping when the square overshoots. The
search has to be *bounded* to live here at all: every fragment in this
development is a total `Reaches` statement, and an unbounded loop that stops
when a condition fails has no such statement. The bound is `n` itself, since
`Nat.sqrt n ≤ n` and each iteration advances the candidate by at most one.

Running the loop a fixed `n` times rather than until it settles is what makes
the invariant say `min (Nat.sqrt n) k` after `k` iterations. The `min` is not
slack: for small `n` the search reaches its answer early and the remaining
iterations must leave it alone, which is exactly what the comparison arm that
does not increment provides.

`sqrtStep` isolates that arithmetic from the register bookkeeping. It is the
only place `Nat.sqrt` is reasoned about; the body lemma above it only moves
values between registers.

The body is given as a concrete list rather than as slot hypotheses. The
reusable pieces below it — the copy, the multiplication, the comparison —
stay parametric, because they are embedded at many different layouts. This
composite is used once, so pinning its internal addresses costs nothing and
collapses what would otherwise be thirty slot hypotheses and forty-five
disjointness side conditions into one `EmbeddedAt` and three inequalities.
The working registers are a contiguous block above `lo` for the same reason:
disjointness becomes arithmetic.

## Main definitions

* `sqrtBodyFrag`: The search loop as a concrete instruction list.

## Theorems

* `sqrtStep`: One upward-search step lands on the next `min` of the search.
* `squareVar_effect`: A register's square is added to another.
-/

namespace LeanBF

namespace Register

/-- One step of the upward search. Having tested `k` candidates the answer so
    far is `min (Nat.sqrt n) k`; testing one more either advances it or, once
    the search has already settled, leaves it where it is. -/
theorem sqrtStep (n m r : Nat) (hm : m + 1 ≤ n) (hr : r = min (Nat.sqrt n) (n - (m + 1))) :
    (if (r + 1) * (r + 1) ≤ n then r + 1 else r) = min (Nat.sqrt n) (n - m) := by
  subst hr
  have hsn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  by_cases hc : (min (Nat.sqrt n) (n - (m + 1)) + 1) * (min (Nat.sqrt n) (n - (m + 1)) + 1) ≤ n
  · -- The candidate still fits, so it becomes the new answer.
    rw [if_pos hc]
    have hle := Nat.le_sqrt.mpr hc
    omega
  · -- It overshoots, so the search has already settled.
    rw [if_neg hc]
    have hgt : ¬ (min (Nat.sqrt n) (n - (m + 1)) + 1 ≤ Nat.sqrt n) :=
      fun h => hc (Nat.le_sqrt.mp h)
    omega

/-- Squaring a register into another: copy it, then multiply the copy in.
    The source survives, since both the copy and the multiplication preserve
    what they read. -/
theorem squareVar_effect (p : Program) (a t v sc base m1 mul exit : Nat)
    (hav : a ≠ v) (hasc : a ≠ sc) (hvsc : v ≠ sc)
    (hat : a ≠ t) (htv : t ≠ v) (htsc : t ≠ sc)
    (hc0 : p[base]? = some (Instruction.jzdec a m1 (base + 1)))
    (hc1 : p[base + 1]? = some (Instruction.inc v (base + 2)))
    (hc2 : p[base + 2]? = some (Instruction.inc sc base))
    (hc3 : p[m1]? = some (Instruction.jzdec sc mul (m1 + 1)))
    (hc4 : p[m1 + 1]? = some (Instruction.inc a m1))
    (hloop : p[mul]? = some (Instruction.jzdec v exit (mul + 1)))
    (h0 : p[mul + 1]? = some (Instruction.jzdec a (mul + 4) (mul + 2)))
    (hi1 : p[mul + 2]? = some (Instruction.inc t (mul + 3)))
    (hi2 : p[mul + 3]? = some (Instruction.inc sc (mul + 1)))
    (hd0 : p[mul + 4]? = some (Instruction.jzdec sc mul (mul + 5)))
    (hd1 : p[mul + 5]? = some (Instruction.inc a (mul + 4))) :
    ∀ (s : State), s.pc = base → s.regs sc = 0 → s.regs v = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs a = s.regs a ∧
        s'.regs v = 0 ∧ s'.regs sc = 0 ∧
        s'.regs t = s.regs t + s.regs a * s.regs a ∧
        ∀ r, r ≠ a → r ≠ t → r ≠ v → r ≠ sc → s'.regs r = s.regs r := by
  intro s hpc hsc hv
  -- Copy the source, so the multiplication has a counter to consume.
  rcases copyBack_effect p a v sc base m1 mul hav hasc hvsc hc0 hc1 hc2 hc3 hc4
    s hpc hsc with ⟨s1, hr1, hpc1, hA1, hV1, hS1, hF1⟩
  -- Multiply the source by the copy.
  rcases mulVar_effect p a v t sc mul exit hat hasc htsc hav (fun hc => htv hc.symm)
    (fun hc => hvsc hc) hloop h0 hi1 hi2 hd0 hd1 s1 hpc1 hS1 with
    ⟨s2, hr2, hpc2, hV2, hA2, hS2, hT2, hF2⟩
  refine ⟨s2, reaches_trans hr1 hr2, hpc2, by rw [hA2, hA1], hV2, hS2, ?_,
    fun r hra hrt hrv hrsc => by rw [hF2 r hra hrt hrsc hrv, hF1 r hra hrv hrsc]⟩
  -- The copy held the source, so the product is the square.
  rw [hT2, hA1, hV1, hv, Nat.zero_add,
    hF1 t (fun hc => hat hc.symm) (fun hc => htv hc) (fun hc => htsc hc)]

/-- The upward search as a concrete fragment, laid out from `base`. Slot `0`
    is the loop head; the body copies the candidate, raises it, squares it,
    compares the square against the input, advances the candidate on the arm
    where it still fits, and clears both working values before returning.

    Clearing the square at the end of every iteration is not tidiness. The
    squaring fragment *adds* to its target, so a square left behind would be
    added to the next one and the comparison would test a running total
    instead of a candidate. -/
def sqrtBodyFrag (nR r lo base exit : Nat) : Program :=
  [.jzdec (lo + 7) exit (base + 1),
   .jzdec r (base + 4) (base + 2), .inc lo (base + 3), .inc (lo + 5) (base + 1),
   .jzdec (lo + 5) (base + 6) (base + 5), .inc r (base + 4),
   .inc lo (base + 7),
   .jzdec lo (base + 10) (base + 8), .inc (lo + 2) (base + 9),
   .inc (lo + 5) (base + 7),
   .jzdec (lo + 5) (base + 12) (base + 11), .inc lo (base + 10),
   .jzdec (lo + 2) (base + 18) (base + 13),
   .jzdec lo (base + 16) (base + 14), .inc (lo + 1) (base + 15),
   .inc (lo + 5) (base + 13),
   .jzdec (lo + 5) (base + 12) (base + 17), .inc lo (base + 16),
   .jzdec (lo + 1) (base + 21) (base + 19), .inc (lo + 3) (base + 20),
   .inc (lo + 6) (base + 18),
   .jzdec (lo + 6) (base + 23) (base + 22), .inc (lo + 1) (base + 21),
   .jzdec nR (base + 26) (base + 24), .inc (lo + 4) (base + 25),
   .inc (lo + 6) (base + 23),
   .jzdec (lo + 6) (base + 28) (base + 27), .inc nR (base + 26),
   .jzdec (lo + 4) (base + 30) (base + 29),
   .jzdec (lo + 3) (base + 28) (base + 28),
   .jzdec (lo + 3) (base + 32) (base + 31),
   .jzdec (lo + 3) (base + 33) (base + 31),
   .inc r (base + 33),
   .jzdec lo (base + 34) (base + 33),
   .jzdec (lo + 1) base (base + 34)]

end Register

end LeanBF
