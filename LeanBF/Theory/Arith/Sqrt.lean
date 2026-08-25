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
* `sqrtBody_effect`: One search iteration tests the next candidate.
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

/-- One iteration of the search. The candidate is copied, raised, and
    squared; the square is compared against the input; and the candidate
    advances only on the arm where the square still fits. Both arms rejoin at
    the shared clear.

    Everything here is register bookkeeping — the only arithmetic fact used
    is `sqrtStep`, applied once at the branch. -/
theorem sqrtBody_effect (p : Program) (nR r lo base exit : Nat)
    (hnr : nR ≠ r) (hn : nR < lo) (hr : r < lo)
    (hemb : EmbeddedAt p base (sqrtBodyFrag nR r lo base exit))
    (n0 : Nat) :
    ∀ (m : Nat) (s : State), s.pc = base + 1 → s.regs (lo + 7) = m →
      s.regs nR = n0 → s.regs r = min (Nat.sqrt n0) (n0 - (m + 1)) →
      (∀ j, j < 7 → s.regs (lo + j) = 0) → m + 1 ≤ n0 →
      ∃ s', Reaches p s s' ∧ s'.pc = base ∧ s'.regs (lo + 7) = m ∧
        s'.regs nR = n0 ∧ s'.regs r = min (Nat.sqrt n0) (n0 - m) ∧
        (∀ j, j < 7 → s'.regs (lo + j) = 0) ∧
        ∀ q, q ≠ nR → q ≠ r → (q < lo ∨ lo + 8 ≤ q) → s'.regs q = s.regs q := by
  intro m s hpc hcnt hnv hrv hz hmn
  have hg := embeddedAt_get p base _ hemb
  -- Stage one: copy the candidate, then raise the copy.
  rcases copyBack_effect p r lo (lo + 5) (base + 1) (base + 4) (base + 6)
    (by omega) (by omega) (by omega)
    (hg 1 _ rfl) (hg 2 _ rfl) (hg 3 _ rfl) (hg 4 _ rfl) (hg 5 _ rfl)
    s hpc (hz 5 (by omega)) with ⟨s1, hr1, hpc1, hR1, hU1, hS1, hF1⟩
  -- Raise the copy to the next candidate.
  have hstepInc : step p s1
      = some { setReg s1 lo (s1.regs lo + 1) with pc := base + 7 } := by
    simp only [step, hpc1, hg 6 _ rfl, setReg]
  set s2 : State := { setReg s1 lo (s1.regs lo + 1) with pc := base + 7 } with hs2
  -- Stage two: square the candidate into `lo + 1`.
  rcases squareVar_effect p lo (lo + 1) (lo + 2) (lo + 5) (base + 7) (base + 10)
    (base + 12) (base + 18) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hg 7 _ rfl) (hg 8 _ rfl) (hg 9 _ rfl) (hg 10 _ rfl) (hg 11 _ rfl)
    (hg 12 _ rfl) (hg 13 _ rfl) (hg 14 _ rfl) (hg 15 _ rfl) (hg 16 _ rfl) (hg 17 _ rfl)
    s2 rfl (by
      simp only [hs2, setReg, if_neg (by omega : lo + 5 ≠ lo)]
      exact hS1)
    (by
      simp only [hs2, setReg, if_neg (by omega : lo + 2 ≠ lo)]
      rw [hF1 (lo + 2) (by omega) (by omega) (by omega)]
      exact hz 2 (by omega)) with ⟨s3, hr3, hpc3, hU3, hV3, hS3, hT3, hF3⟩
  -- The candidate's square, which is what the comparison tests.
  have hcand : s3.regs (lo + 1) = (min (Nat.sqrt n0) (n0 - (m + 1)) + 1) *
      (min (Nat.sqrt n0) (n0 - (m + 1)) + 1) := by
    have hU2 : s2.regs lo = min (Nat.sqrt n0) (n0 - (m + 1)) + 1 := by
      have hz0 : s.regs lo = 0 := by
        have := hz 0 (by omega)
        rwa [Nat.add_zero] at this
      simp only [hs2, setReg, hU1, hrv, hz0, Nat.zero_add, if_true]
    have hT2 : s2.regs (lo + 1) = 0 := by
      simp only [hs2, setReg, if_neg (by omega : lo + 1 ≠ lo)]
      rw [hF1 (lo + 1) (by omega) (by omega) (by omega)]
      exact hz 1 (by omega)
    rw [hT3, hU2, hT2, Nat.zero_add]
  -- Stage three: compare the input against the square.
  rcases cmpBranch_effect p nR (lo + 1) (lo + 3) (lo + 4) (lo + 6)
    (base + 18) (base + 21) (base + 23) (base + 26) (base + 28) (base + 30) (base + 31)
    (base + 33) (base + 32)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (hg 18 _ rfl) (hg 19 _ rfl) (hg 20 _ rfl) (hg 21 _ rfl) (hg 22 _ rfl)
    (hg 23 _ rfl) (hg 24 _ rfl) (hg 25 _ rfl) (hg 26 _ rfl) (hg 27 _ rfl)
    (hg 28 _ rfl) (hg 29 _ rfl) (hg 30 _ rfl) (hg 31 _ rfl)
    s3 hpc3
    (by
      rw [hF3 (lo + 6) (by omega) (by omega) (by omega) (by omega), hs2]
      simp only [setReg, if_neg (by omega : lo + 6 ≠ lo)]
      rw [hF1 (lo + 6) (by omega) (by omega) (by omega)]
      exact hz 6 (by omega))
    (by
      rw [hF3 (lo + 3) (by omega) (by omega) (by omega) (by omega), hs2]
      simp only [setReg, if_neg (by omega : lo + 3 ≠ lo)]
      rw [hF1 (lo + 3) (by omega) (by omega) (by omega)]
      exact hz 3 (by omega))
    (by
      rw [hF3 (lo + 4) (by omega) (by omega) (by omega) (by omega), hs2]
      simp only [setReg, if_neg (by omega : lo + 4 ≠ lo)]
      rw [hF1 (lo + 4) (by omega) (by omega) (by omega)]
      exact hz 4 (by omega)) with
    ⟨s4, hr4, hN4, hT4, hSc4, hC4, hW4, hFcmp, hpc4⟩
  -- The input as the comparison saw it.
  have hN3 : s3.regs nR = n0 := by
    rw [hF3 nR (by omega) (by omega) (by omega) (by omega), hs2]
    simp only [setReg, if_neg (by omega : nR ≠ lo)]
    rw [hF1 nR (by omega) (by omega) (by omega)]
    exact hnv
  -- The two arms differ only in whether the candidate advances. Both land on
  -- the shared clear, so state where that clear starts and what `r` holds.
  have harm : ∃ s5, Reaches p s4 s5 ∧ s5.pc = base + 33 ∧
      s5.regs r = min (Nat.sqrt n0) (n0 - m) ∧
      ∀ q, q ≠ r → s5.regs q = s4.regs q := by
    by_cases hlt : n0 < (min (Nat.sqrt n0) (n0 - (m + 1)) + 1) *
        (min (Nat.sqrt n0) (n0 - (m + 1)) + 1)
    · -- Overshoot: the candidate stays where it is.
      refine ⟨s4, Reaches.refl _, ?_, ?_, fun q _ => rfl⟩
      · rw [hpc4, hN3, hcand, if_pos hlt]
      · rw [hFcmp r (by omega) (by omega) (by omega) (by omega) (by omega),
          hF3 r (by omega) (by omega) (by omega) (by omega), hs2]
        simp only [setReg, if_neg (by omega : r ≠ lo)]
        rw [hR1, hrv]
        have hstep := sqrtStep n0 m (min (Nat.sqrt n0) (n0 - (m + 1))) hmn rfl
        rw [if_neg (by omega : ¬ (min (Nat.sqrt n0) (n0 - (m + 1)) + 1) *
          (min (Nat.sqrt n0) (n0 - (m + 1)) + 1) ≤ n0)] at hstep
        exact hstep
    · -- It fits: the candidate advances by one.
      have hpcGE : s4.pc = base + 32 := by rw [hpc4, hN3, hcand, if_neg hlt]
      have hstep : step p s4 = some { setReg s4 r (s4.regs r + 1) with pc := base + 33 } := by
        simp only [step, hpcGE, hg 32 _ rfl, setReg]
      refine ⟨_, Reaches.step _ _ _ hstep (Reaches.refl _), rfl, ?_, ?_⟩
      · change (if r = r then s4.regs r + 1 else s4.regs r) = min (Nat.sqrt n0) (n0 - m)
        rw [if_pos rfl, hFcmp r (by omega) (by omega) (by omega) (by omega) (by omega),
          hF3 r (by omega) (by omega) (by omega) (by omega), hs2]
        simp only [setReg, if_neg (by omega : r ≠ lo)]
        rw [hR1, hrv]
        have hstep := sqrtStep n0 m (min (Nat.sqrt n0) (n0 - (m + 1))) hmn rfl
        rw [if_pos (by omega : (min (Nat.sqrt n0) (n0 - (m + 1)) + 1) *
          (min (Nat.sqrt n0) (n0 - (m + 1)) + 1) ≤ n0)] at hstep
        exact hstep
      · intro q hqr
        change (if q = r then s4.regs r + 1 else s4.regs q) = s4.regs q
        rw [if_neg hqr]
  rcases harm with ⟨s5, hr5, hpc5, hR5, hF5⟩
  -- The shared clears: the candidate copy, then its square.
  have hclr1 := clear_reaches p lo (base + 33) (base + 34) (hg 33 _ rfl) (s5.regs lo) s5 hpc5 rfl
  set s6 : State := { pc := base + 34, regs := fun i => if i = lo then 0 else s5.regs i } with hs6
  have hclr2 := clear_reaches p (lo + 1) (base + 34) base (hg 34 _ rfl)
    (s6.regs (lo + 1)) s6 rfl rfl
  refine ⟨_, reaches_trans hr1 (Reaches.step _ _ _ hstepInc (reaches_trans hr3
    (reaches_trans hr4 (reaches_trans hr5 (reaches_trans hclr1 hclr2))))), rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- The counter is untouched by everything the body does.
    change (if lo + 7 = lo + 1 then 0 else s6.regs (lo + 7)) = m
    rw [if_neg (by omega)]
    simp only [hs6, if_neg (by omega : lo + 7 ≠ lo)]
    rw [hF5 (lo + 7) (by omega),
      hFcmp (lo + 7) (by omega) (by omega) (by omega) (by omega) (by omega),
      hF3 (lo + 7) (by omega) (by omega) (by omega) (by omega), hs2]
    simp only [setReg, if_neg (by omega : lo + 7 ≠ lo)]
    rw [hF1 (lo + 7) (by omega) (by omega) (by omega)]
    exact hcnt
  · -- The comparison restores the input it read.
    change (if nR = lo + 1 then 0 else s6.regs nR) = n0
    rw [if_neg (by omega)]
    simp only [hs6, if_neg (by omega : nR ≠ lo)]
    rw [hF5 nR (by omega), hN4, hN3]
  · -- The candidate, advanced or not by the arm that ran.
    change (if r = lo + 1 then 0 else s6.regs r) = min (Nat.sqrt n0) (n0 - m)
    rw [if_neg (by omega)]
    simp only [hs6, if_neg (by omega : r ≠ lo)]
    exact hR5
  · -- Every working register is clear again: the comparison cleaned its own,
    -- and the two clears empty the candidate copy and its square.
    intro j hj
    change (if lo + j = lo + 1 then 0 else s6.regs (lo + j)) = 0
    by_cases hj1 : j = 1
    · rw [hj1, if_pos rfl]
    · rw [if_neg (by omega)]
      simp only [hs6]
      by_cases hj0 : j = 0
      · rw [hj0, Nat.add_zero, if_pos rfl]
      · rw [if_neg (by omega)]
        rw [hF5 (lo + j) (by omega)]
        -- The comparison left its three working registers clear.
        match j, hj, hj0, hj1 with
        | 2, _, _, _ =>
            rw [hFcmp (lo + 2) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact hV3
        | 3, _, _, _ => exact hW4
        | 4, _, _, _ => exact hC4
        | 5, _, _, _ =>
            rw [hFcmp (lo + 5) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact hS3
        | 6, _, _, _ => exact hSc4
  · -- Nothing outside the named registers and the working block moves.
    intro q hqn hqr hqout
    change (if q = lo + 1 then 0 else s6.regs q) = s.regs q
    rw [if_neg (by omega)]
    simp only [hs6, if_neg (by omega : q ≠ lo)]
    rw [hF5 q hqr, hFcmp q hqn (by omega) (by omega) (by omega) (by omega),
      hF3 q (by omega) (by omega) (by omega) (by omega), hs2]
    simp only [setReg, if_neg (by omega : q ≠ lo)]
    rw [hF1 q hqr (by omega) (by omega)]

end Register

end LeanBF
