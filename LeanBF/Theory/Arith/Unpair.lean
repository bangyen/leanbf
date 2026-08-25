/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Pair
import Mathlib.Tactic.IntervalCases

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
* `unpairVar_effect`: The fragment computes `Nat.unpair` of its input.
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

/-- The unpairing function: both halves of `Nat.unpair` land in the two
    output registers, the input survives, and the working block ends clear. -/
theorem unpairVar_effect (p : Program) (nR o1 o2 lo base exit : Nat)
    (hn1 : nR ≠ o1) (hn2 : nR ≠ o2) (h12 : o1 ≠ o2)
    (hnl : nR < lo) (h1l : o1 < lo) (h2l : o2 < lo)
    (hemb : EmbeddedAt p base (unpairFrag nR o1 o2 lo base exit)) :
    ∀ (s : State), s.pc = base → s.regs o1 = 0 → s.regs o2 = 0 →
      (∀ j, j < 16 → s.regs (lo + j) = 0) →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs nR = s.regs nR ∧
        s'.regs o1 = (Nat.unpair (s.regs nR)).1 ∧
        s'.regs o2 = (Nat.unpair (s.regs nR)).2 ∧
        (∀ j, j < 16 → s'.regs (lo + j) = 0) ∧
        ∀ q, q ≠ nR → q ≠ o1 → q ≠ o2 → (q < lo ∨ lo + 16 ≤ q) → s'.regs q = s.regs q := by
  intro s hpc ho1 ho2 hz
  have hembA := embeddedAt_append_left p base _ _ hemb
  have hembB := embeddedAt_append_right p base _ _ hemb
  -- Stage A: the square root of the input lands in `lo`.
  rcases sqrtVar_effect p nR lo (lo + 2) base (base + 40)
    (by omega) (by omega) (by omega) hembA s hpc
    (by simpa only [Nat.add_zero] using hz 0 (by omega))
    (fun j hj => by
      have := hz (j + 2) (by omega)
      rwa [show lo + (j + 2) = lo + 2 + j by omega] at this) with
    ⟨s1, hr1, hpc1, hN1, hS1, hZ1, hF1⟩
  have hgb := embeddedAt_get p (base + 40) _ hembB
  -- The registers above the search's block never moved, so they are clear.
  have hup : ∀ j, 10 ≤ j → j < 16 → s1.regs (lo + j) = 0 := by
    intro j hj1 hj2
    rw [hF1 (lo + j) (by omega) (by omega) (by omega)]
    exact hz j hj2
  have hrem1 : s1.regs (lo + 1) = 0 := by
    rw [hF1 (lo + 1) (by omega) (by omega) (by omega)]
    exact hz 1 (by omega)
  have hout11 : s1.regs o1 = 0 := by
    rw [hF1 o1 (by omega) (by omega) (by omega)]
    exact ho1
  have hout21 : s1.regs o2 = 0 := by
    rw [hF1 o2 (by omega) (by omega) (by omega)]
    exact ho2
  -- Stage B: square the root back, into `lo + 10`.
  rcases squareVar_effect p lo (lo + 10) (lo + 11) (lo + 12) (base + 40) (base + 43)
    (base + 45) (base + 51) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa only [Nat.add_zero] using hgb 0 _ rfl) (hgb 1 _ rfl) (hgb 2 _ rfl)
    (hgb 3 _ rfl) (hgb 4 _ rfl) (hgb 5 _ rfl) (hgb 6 _ rfl) (hgb 7 _ rfl)
    (hgb 8 _ rfl) (hgb 9 _ rfl) (hgb 10 _ rfl)
    s1 hpc1 (hup 12 (by omega) (by omega)) (hup 11 (by omega) (by omega)) with
    ⟨s2, hr2, hpc2, hR2, hV2, hSc2, hSq2, hF2⟩
  -- Stage C: the remainder is the input less the square.
  rcases subVar_effect p nR (lo + 10) (lo + 1) (lo + 14) (lo + 12) (base + 51)
    (base + 54) (base + 56) (base + 59) (base + 61) (base + 63)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (hgb 11 _ rfl) (hgb 12 _ rfl) (hgb 13 _ rfl) (hgb 14 _ rfl) (hgb 15 _ rfl)
    (hgb 16 _ rfl) (hgb 17 _ rfl) (hgb 18 _ rfl) (hgb 19 _ rfl) (hgb 20 _ rfl)
    (hgb 21 _ rfl) (hgb 22 _ rfl)
    s2 hpc2 hSc2
    (by rw [hF2 (lo + 1) (by omega) (by omega) (by omega) (by omega)]; exact hrem1)
    (by
      rw [hF2 (lo + 14) (by omega) (by omega) (by omega) (by omega)]
      exact hup 14 (by omega) (by omega)) with
    ⟨s3, hr3, hpc3, hN3, hSq3, hSc3, hC3, hD3, hF3⟩
  -- The square survives the subtraction, so it needs clearing.
  have hclr := clear_reaches p (lo + 10) (base + 63) (base + 64) (hgb 23 _ rfl)
    (s3.regs (lo + 10)) s3 hpc3 rfl
  set s4 : State :=
    { pc := base + 64, regs := fun i => if i = lo + 10 then 0 else s3.regs i } with hs4
  -- The root and the remainder, as the comparison will see them.
  have hroot : s4.regs lo = Nat.sqrt (s.regs nR) := by
    simp only [hs4, if_neg (by omega : lo ≠ lo + 10)]
    rw [hF3 lo (by omega) (by omega) (by omega) (by omega) (by omega), hR2, hS1]
  have hrem : s4.regs (lo + 1) = s.regs nR - Nat.sqrt (s.regs nR) * Nat.sqrt (s.regs nR) := by
    simp only [hs4, if_neg (by omega : lo + 1 ≠ lo + 10)]
    rw [hD3, hSq2, hup 10 (by omega) (by omega), Nat.zero_add, hS1,
      hF2 nR (by omega) (by omega) (by omega) (by omega), hN1]
  have hin4 : s4.regs nR = s.regs nR := by
    simp only [hs4, if_neg (by omega : nR ≠ lo + 10)]
    rw [hN3, hF2 nR (by omega) (by omega) (by omega) (by omega), hN1]
  -- Stage D: compare the remainder against the root.
  rcases cmpBranch_effect p (lo + 1) lo (lo + 13) (lo + 14) (lo + 15)
    (base + 64) (base + 67) (base + 69) (base + 72) (base + 74) (base + 76) (base + 77)
    (base + 78) (base + 82)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (hgb 24 _ rfl) (hgb 25 _ rfl) (hgb 26 _ rfl) (hgb 27 _ rfl) (hgb 28 _ rfl)
    (hgb 29 _ rfl) (hgb 30 _ rfl) (hgb 31 _ rfl) (hgb 32 _ rfl) (hgb 33 _ rfl)
    (hgb 34 _ rfl) (hgb 35 _ rfl) (hgb 36 _ rfl) (hgb 37 _ rfl)
    s4 rfl
    (by
      simp only [hs4, if_neg (by omega : lo + 15 ≠ lo + 10)]
      rw [hF3 (lo + 15) (by omega) (by omega) (by omega) (by omega) (by omega),
        hF2 (lo + 15) (by omega) (by omega) (by omega) (by omega)]
      exact hup 15 (by omega) (by omega))
    (by
      simp only [hs4, if_neg (by omega : lo + 13 ≠ lo + 10)]
      rw [hF3 (lo + 13) (by omega) (by omega) (by omega) (by omega) (by omega),
        hF2 (lo + 13) (by omega) (by omega) (by omega) (by omega)]
      exact hup 13 (by omega) (by omega))
    (by
      simp only [hs4, if_neg (by omega : lo + 14 ≠ lo + 10)]
      exact hC3) with ⟨s5, hr5, hD5, hR5, hSc5, hC5, hW5, hF5, hpc5⟩
  -- The values the arms drain, and the state they start from.
  have hd5 : s5.regs (lo + 1) = s.regs nR - Nat.sqrt (s.regs nR) * Nat.sqrt (s.regs nR) := by
    rw [hD5, hrem]
  have hs5 : s5.regs lo = Nat.sqrt (s.regs nR) := by rw [hR5, hroot]
  have hin5 : s5.regs nR = s.regs nR := by
    rw [hF5 nR (by omega) (by omega) (by omega) (by omega) (by omega), hin4]
  have ho15 : s5.regs o1 = 0 := by
    rw [hF5 o1 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [hs4, if_neg (by omega : o1 ≠ lo + 10)]
    rw [hF3 o1 (by omega) (by omega) (by omega) (by omega) (by omega),
      hF2 o1 (by omega) (by omega) (by omega) (by omega)]
    exact hout11
  have ho25 : s5.regs o2 = 0 := by
    rw [hF5 o2 (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [hs4, if_neg (by omega : o2 ≠ lo + 10)]
    rw [hF3 o2 (by omega) (by omega) (by omega) (by omega) (by omega),
      hF2 o2 (by omega) (by omega) (by omega) (by omega)]
    exact hout21
  -- The search's own working block came back clear and nothing since touched it.
  have hsearch : ∀ j, 2 ≤ j → j < 10 → s5.regs (lo + j) = 0 := by
    intro j hj1 hj2
    rw [hF5 (lo + j) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [hs4, if_neg (by omega : lo + j ≠ lo + 10)]
    rw [hF3 (lo + j) (by omega) (by omega) (by omega) (by omega) (by omega),
      hF2 (lo + j) (by omega) (by omega) (by omega) (by omega)]
    have := hZ1 (j - 2) (by omega)
    rwa [show lo + 2 + (j - 2) = lo + j by omega] at this
  -- Every working register other than the root and the remainder is clear.
  have hz5 : ∀ j, j < 16 → j ≠ 0 → j ≠ 1 → s5.regs (lo + j) = 0 := by
    intro j hj hj0 hj1
    by_cases hlow : j < 10
    · exact hsearch j (by omega) hlow
    · -- Above the search's block: the square, the copy scratch, and the
      -- comparison's three, all cleared by the stages that used them.
      have hclr10 : s5.regs (lo + 10) = 0 := by
        rw [hF5 (lo + 10) (by omega) (by omega) (by omega) (by omega) (by omega)]
        simp only [hs4, if_true]
      have hclr11 : s5.regs (lo + 11) = 0 := by
        rw [hF5 (lo + 11) (by omega) (by omega) (by omega) (by omega) (by omega)]
        simp only [hs4, if_neg (by omega : lo + 11 ≠ lo + 10)]
        rw [hF3 (lo + 11) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hV2
      have hclr12 : s5.regs (lo + 12) = 0 := by
        rw [hF5 (lo + 12) (by omega) (by omega) (by omega) (by omega) (by omega)]
        simp only [hs4, if_neg (by omega : lo + 12 ≠ lo + 10)]
        exact hSc3
      interval_cases j
      · exact hclr10
      · exact hclr11
      · exact hclr12
      · exact hW5
      · exact hC5
      · exact hSc5
  by_cases hlt : s.regs nR - Nat.sqrt (s.regs nR) * Nat.sqrt (s.regs nR) < Nat.sqrt (s.regs nR)
  · -- The remainder is below the root: it is the first answer, the root the
    -- second, and both are drained straight out.
    have hpcLT : s5.pc = base + 78 := by
      rw [hpc5, hrem, hroot, if_pos hlt]
    have hdrain1 := drain_reaches p (lo + 1) o1 (base + 78) (base + 80) (by omega)
      (hgb 38 _ rfl) (hgb 39 _ rfl) (s5.regs (lo + 1)) s5 hpcLT rfl
    set s6 : State := drained (lo + 1) o1 (base + 80) (s5.regs (lo + 1)) s5 with hs6
    have hdrain2 := drain_reaches p lo o2 (base + 80) exit (by omega)
      (hgb 40 _ rfl) (hgb 41 _ rfl) (s6.regs lo) s6 (by simp only [hs6, drained]) rfl
    refine ⟨_, reaches_trans hr1 (reaches_trans hr2 (reaches_trans hr3
      (reaches_trans hclr (reaches_trans hr5
        (reaches_trans hdrain1 hdrain2))))), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [drained, if_neg (by omega : nR ≠ lo), if_neg (by omega : nR ≠ o2),
        if_neg (by omega : nR ≠ lo + 1), if_neg (by omega : nR ≠ o1), hs6]
      exact hin5
    · -- The first answer is the remainder.
      simp only [drained, if_neg (by omega : o1 ≠ lo), if_neg (by omega : o1 ≠ o2),
        if_true, hs6, if_neg (by omega : o1 ≠ lo + 1)]
      rw [ho15, Nat.zero_add, hd5]
      simp only [Nat.unpair, if_pos hlt]
    · -- The second is the root.
      simp only [drained, if_true, hs6,
        if_neg (by omega : o2 ≠ lo + 1), if_neg (by omega : o2 ≠ o1)]
      rw [ho25, Nat.zero_add]
      simp only [if_neg (by omega : o2 ≠ lo), if_neg (by omega : lo ≠ lo + 1),
        if_neg (by omega : lo ≠ o1), hs5]
      simp only [Nat.unpair, if_pos hlt]
    · intro j hj
      by_cases hj0 : j = 0
      · simp only [hj0, Nat.add_zero, drained, if_true]
      · by_cases hj1 : j = 1
        · simp only [hj1, drained, if_neg (by omega : lo + 1 ≠ lo),
            if_neg (by omega : lo + 1 ≠ o2), hs6, if_true]
        · simp only [drained, if_neg (by omega : lo + j ≠ lo),
            if_neg (by omega : lo + j ≠ o2), hs6, if_neg (by omega : lo + j ≠ lo + 1),
            if_neg (by omega : lo + j ≠ o1)]
          exact hz5 j hj hj0 hj1
    · intro q hqn hq1 hq2 hqr
      simp only [drained, if_neg (by omega : q ≠ lo), if_neg hq2, hs6,
        if_neg (by omega : q ≠ lo + 1), if_neg hq1]
      rw [hF5 q (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp only [hs4, if_neg (by omega : q ≠ lo + 10)]
      rw [hF3 q hqn (by omega) (by omega) (by omega) (by omega),
        hF2 q (by omega) (by omega) (by omega) (by omega),
        hF1 q hqn (by omega) (by omega)]
  · -- The remainder is at least the root: the root is the first answer, and
    -- the second is what is left after taking it off the remainder.
    have hpcGE : s5.pc = base + 82 := by
      rw [hpc5, hrem, hroot, if_neg hlt]
    -- Copy the root into a counter, since it is still needed as an answer.
    rcases copyBack_effect p lo (lo + 14) (lo + 15) (base + 82) (base + 85) (base + 87)
      (by omega) (by omega) (by omega)
      (hgb 42 _ rfl) (hgb 43 _ rfl) (hgb 44 _ rfl) (hgb 45 _ rfl) (hgb 46 _ rfl)
      s5 hpcGE hSc5 with ⟨s6, hr6, hpc6, hR6, hCn6, hSc6, hF6⟩
    -- Take the root off the remainder.
    rcases subLoop_effect p (lo + 1) (lo + 14) (base + 87) (base + 89) (by omega)
      (hgb 47 _ rfl) (hgb 48 _ rfl) s6 hpc6 with ⟨s7, hr7, hpc7, hCn7, hD7, hF7⟩
    -- Drain the root out as the first answer, the rest as the second.
    have hdrain1 := drain_reaches p lo o1 (base + 89) (base + 91) (by omega)
      (hgb 49 _ rfl) (hgb 50 _ rfl) (s7.regs lo) s7 hpc7 rfl
    set s8 : State := drained lo o1 (base + 91) (s7.regs lo) s7 with hs8
    have hdrain2 := drain_reaches p (lo + 1) o2 (base + 91) exit (by omega)
      (hgb 51 _ rfl) (hgb 52 _ rfl) (s8.regs (lo + 1)) s8
      (by simp only [hs8, drained]) rfl
    refine ⟨_, reaches_trans hr1 (reaches_trans hr2 (reaches_trans hr3
      (reaches_trans hclr (reaches_trans hr5 (reaches_trans hr6
        (reaches_trans hr7 (reaches_trans hdrain1 hdrain2))))))), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hs8, drained, if_neg (by omega : nR ≠ lo + 1), if_neg (by omega : nR ≠ o2),
        if_neg (by omega : nR ≠ lo), if_neg (by omega : nR ≠ o1)]
      rw [hF7 nR (by omega) (by omega),
        hF6 nR (by omega) (by omega) (by omega), hin5]
    · -- The first answer is the root, drained out whole.
      simp only [hs8, drained, if_neg (by omega : o1 ≠ lo + 1), if_neg (by omega : o1 ≠ o2),
        if_neg (by omega : o1 ≠ lo), if_true]
      rw [hF7 o1 (by omega) (by omega), hF6 o1 (by omega) (by omega) (by omega), ho15,
        Nat.zero_add, hF7 lo (by omega) (by omega), hR6, hs5]
      simp only [Nat.unpair, if_neg hlt]
    · -- The second is the remainder less the root.
      simp only [hs8, drained, if_neg (by omega : o2 ≠ lo + 1), if_neg (by omega : o2 ≠ lo),
        if_neg (by omega : o2 ≠ o1), if_neg (by omega : lo + 1 ≠ lo),
        if_neg (by omega : lo + 1 ≠ o1)]
      rw [hF7 o2 (by omega) (by omega), hF6 o2 (by omega) (by omega) (by omega), ho25,
        Nat.zero_add]
      simp only [if_true]
      rw [hD7, hCn6, hC5, Nat.zero_add, hs5,
        hF6 (lo + 1) (by omega) (by omega) (by omega), hd5]
      simp only [Nat.unpair, if_neg hlt]
    · intro j hj
      by_cases hj1 : j = 1
      · simp only [hj1, hs8, drained, if_true]
      · by_cases hj0 : j = 0
        · simp only [hj0, Nat.add_zero, hs8, drained,
            if_neg (by omega : lo ≠ lo + 1), if_neg (by omega : lo ≠ o2), if_true]
        · simp only [hs8, drained, if_neg (by omega : lo + j ≠ lo + 1),
            if_neg (by omega : lo + j ≠ o2), if_neg (by omega : lo + j ≠ lo),
            if_neg (by omega : lo + j ≠ o1)]
          by_cases hj14 : j = 14
          · rw [hj14]
            exact hCn7
          · rw [hF7 (lo + j) (by omega) (by omega)]
            by_cases hj15 : j = 15
            · rw [hj15]
              exact hSc6
            · rw [hF6 (lo + j) (by omega) (by omega) (by omega)]
              exact hz5 j hj hj0 hj1
    · intro q hqn hq1 hq2 hqr
      simp only [hs8, drained, if_neg (by omega : q ≠ lo + 1), if_neg hq2,
        if_neg (by omega : q ≠ lo), if_neg hq1]
      rw [hF7 q (by omega) (by omega), hF6 q (by omega) (by omega) (by omega),
        hF5 q (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp only [hs4, if_neg (by omega : q ≠ lo + 10)]
      rw [hF3 q hqn (by omega) (by omega) (by omega) (by omega),
        hF2 q (by omega) (by omega) (by omega) (by omega),
        hF1 q hqn (by omega) (by omega)]

end Register

end LeanBF
