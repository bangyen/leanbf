/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith.Sqrt

/-!
# The Pairing Function

`Nat.pair a b` is `b * b + a` when `a < b` and `a * a + a + b` otherwise, so a
fragment for it is a comparison whose two arms compute different polynomials
in the two operands.

Both arms need to read their operands more than once — squaring one of them
and then adding it again — which is why every read here goes through the
non-destructive copy. Nothing is consumed except the copies.

Like the square-root search this is a one-use composite, so it is a concrete
list with its addresses pinned rather than a lemma with forty slot
hypotheses. The reusable pieces underneath it stay parametric.

## Main definitions

* `pairFrag`: The pairing function as a concrete instruction list.

## Theorems

* `pairFrag_length`: The fragment occupies fifty-one slots.
* `pairVar_effect`: The fragment computes `Nat.pair` of its two operands.
-/

namespace LeanBF

namespace Register

/-- The pairing function, laid out from `base`. The comparison occupies the
    first fourteen slots and selects an arm; the arm starting at `base + 14`
    computes `b * b + a`, and the one at `base + 30` computes
    `a * a + a + b`. Both leave the operands as they found them.

    The working block runs from `lo`: `lo + 2` is the multiplication
    counter, `lo + 3`, `lo + 4` and `lo + 6` are what the comparison
    consumes, and `lo + 5` is the copy scratch. -/
def pairFrag (a b out lo base exit : Nat) : Program :=
  [.jzdec b (base + 3) (base + 1), .inc (lo + 3) (base + 2), .inc (lo + 6) base,
   .jzdec (lo + 6) (base + 5) (base + 4), .inc b (base + 3),
   .jzdec a (base + 8) (base + 6), .inc (lo + 4) (base + 7), .inc (lo + 6) (base + 5),
   .jzdec (lo + 6) (base + 10) (base + 9), .inc a (base + 8),
   .jzdec (lo + 4) (base + 12) (base + 11),
   .jzdec (lo + 3) (base + 10) (base + 10),
   .jzdec (lo + 3) (base + 30) (base + 13),
   .jzdec (lo + 3) (base + 14) (base + 13),
   .jzdec b (base + 17) (base + 15), .inc (lo + 2) (base + 16),
   .inc (lo + 5) (base + 14),
   .jzdec (lo + 5) (base + 19) (base + 18), .inc b (base + 17),
   .jzdec (lo + 2) (base + 25) (base + 20),
   .jzdec b (base + 23) (base + 21), .inc out (base + 22), .inc (lo + 5) (base + 20),
   .jzdec (lo + 5) (base + 19) (base + 24), .inc b (base + 23),
   .jzdec a (base + 28) (base + 26), .inc out (base + 27), .inc (lo + 5) (base + 25),
   .jzdec (lo + 5) exit (base + 29), .inc a (base + 28),
   .jzdec a (base + 33) (base + 31), .inc (lo + 2) (base + 32),
   .inc (lo + 5) (base + 30),
   .jzdec (lo + 5) (base + 35) (base + 34), .inc a (base + 33),
   .jzdec (lo + 2) (base + 41) (base + 36),
   .jzdec a (base + 39) (base + 37), .inc out (base + 38), .inc (lo + 5) (base + 36),
   .jzdec (lo + 5) (base + 35) (base + 40), .inc a (base + 39),
   .jzdec a (base + 44) (base + 42), .inc out (base + 43), .inc (lo + 5) (base + 41),
   .jzdec (lo + 5) (base + 46) (base + 45), .inc a (base + 44),
   .jzdec b (base + 49) (base + 47), .inc out (base + 48), .inc (lo + 5) (base + 46),
   .jzdec (lo + 5) exit (base + 50), .inc b (base + 49)]

theorem pairFrag_length (a b out lo base exit : Nat) :
    (pairFrag a b out lo base exit).length = 51 := rfl

/-- The pairing function. The comparison picks the arm; each arm squares one
    operand and adds the other, all through non-destructive copies, so both
    operands survive and the working block ends clear. -/
theorem pairVar_effect (p : Program) (a b out lo base exit : Nat)
    (hab : a ≠ b) (hao : a ≠ out) (hbo : b ≠ out)
    (ha : a < lo) (hb : b < lo) (ho : out < lo)
    (hemb : EmbeddedAt p base (pairFrag a b out lo base exit)) :
    ∀ (s : State), s.pc = base → s.regs out = 0 →
      (∀ j, j < 8 → s.regs (lo + j) = 0) →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs a = s.regs a ∧
        s'.regs b = s.regs b ∧ s'.regs out = Nat.pair (s.regs a) (s.regs b) ∧
        (∀ j, j < 8 → s'.regs (lo + j) = 0) ∧
        ∀ q, q ≠ a → q ≠ b → q ≠ out → (q < lo ∨ lo + 8 ≤ q) → s'.regs q = s.regs q := by
  intro s hpc hout hz
  have hg := embeddedAt_get p base _ hemb
  -- The comparison, whose arms are the two branches of `Nat.pair`.
  rcases cmpBranch_effect p a b (lo + 3) (lo + 4) (lo + 6) base (base + 3) (base + 5)
    (base + 8) (base + 10) (base + 12) (base + 13) (base + 14) (base + 30)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hab (by omega) (by omega) (by omega)
    (by simpa only [Nat.add_zero] using hg 0 _ rfl) (hg 1 _ rfl)
    (by simpa only [Nat.add_zero] using hg 2 _ rfl) (hg 3 _ rfl) (hg 4 _ rfl)
    (hg 5 _ rfl) (hg 6 _ rfl) (hg 7 _ rfl) (hg 8 _ rfl) (hg 9 _ rfl)
    (hg 10 _ rfl) (hg 11 _ rfl) (hg 12 _ rfl) (hg 13 _ rfl)
    s hpc (hz 6 (by omega)) (hz 3 (by omega)) (hz 4 (by omega)) with
    ⟨s1, hr1, hA1, hB1, hS1, hC1, hW1, hF1, hpc1⟩
  -- The working registers the arms use are still clear after the comparison.
  have hz1 : ∀ j, j < 8 → s1.regs (lo + j) = 0 := by
    intro j hj
    match j, hj with
    | 3, _ => exact hW1
    | 4, _ => exact hC1
    | 6, _ => exact hS1
    | 0, _ => rw [Nat.add_zero,
                hF1 lo (by omega) (by omega) (by omega) (by omega) (by omega)]
              simpa only [Nat.add_zero] using hz 0 (by omega)
    | 1, _ => rw [hF1 (lo + 1) (by omega) (by omega) (by omega) (by omega) (by omega)]
              exact hz 1 (by omega)
    | 2, _ => rw [hF1 (lo + 2) (by omega) (by omega) (by omega) (by omega) (by omega)]
              exact hz 2 (by omega)
    | 5, _ => rw [hF1 (lo + 5) (by omega) (by omega) (by omega) (by omega) (by omega)]
              exact hz 5 (by omega)
    | 7, _ => rw [hF1 (lo + 7) (by omega) (by omega) (by omega) (by omega) (by omega)]
              exact hz 7 (by omega)
  have hout1 : s1.regs out = 0 := by
    rw [hF1 out (fun hc => hao hc.symm) (fun hc => hbo hc.symm) (by omega) (by omega) (by omega)]
    exact hout
  by_cases hlt : s.regs a < s.regs b
  · -- The smaller-first arm: the output is `b * b + a`.
    have hpcLT : s1.pc = base + 14 := by rw [hpc1, if_pos hlt]
    -- Square `b` into the output.
    rcases squareVar_effect p b out (lo + 2) (lo + 5) (base + 14) (base + 17)
      (base + 19) (base + 25) (by omega) (by omega) (by omega)
      (fun hc => hbo hc) (by omega) (by omega)
      (hg 14 _ rfl) (hg 15 _ rfl) (hg 16 _ rfl) (hg 17 _ rfl) (hg 18 _ rfl)
      (hg 19 _ rfl) (hg 20 _ rfl) (hg 21 _ rfl) (hg 22 _ rfl) (hg 23 _ rfl) (hg 24 _ rfl)
      s1 hpcLT (hz1 5 (by omega)) (hz1 2 (by omega)) with
      ⟨s2, hr2, hpc2, hB2, hV2, hSc2, hO2, hF2⟩
    -- Add `a`, which the copy leaves in place.
    rcases copyBack_effect p a out (lo + 5) (base + 25) (base + 28) exit
      (fun hc => hao hc) (by omega) (by omega)
      (hg 25 _ rfl) (hg 26 _ rfl) (hg 27 _ rfl) (hg 28 _ rfl) (hg 29 _ rfl)
      s2 hpc2 hSc2 with ⟨s3, hr3, hpc3, hA3, hO3, hSc3, hF3⟩
    refine ⟨s3, reaches_trans hr1 (reaches_trans hr2 hr3), hpc3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA3, hF2 a (by omega) (fun hc => hao hc) (by omega) (by omega), hA1]
    · rw [hF3 b (fun hc => hab hc.symm) (fun hc => hbo hc) (by omega), hB2, hB1]
    · -- `b * b` from the squaring, then `a` from the copy.
      rw [hO3, hO2, hout1, Nat.zero_add,
        hF2 a (by omega) (fun hc => hao hc) (by omega) (by omega), hA1, hB1,
        Nat.pair, if_pos hlt]
    · intro j hj
      match j, hj with
      | 5, _ => exact hSc3
      | 2, _ => rw [hF3 (lo + 2) (by omega) (by omega) (by omega)]
                exact hV2
      | 0, _ => rw [Nat.add_zero, hF3 lo (by omega) (by omega) (by omega),
                  hF2 lo (by omega) (by omega) (by omega) (by omega)]
                simpa only [Nat.add_zero] using hz1 0 (by omega)
      | 1, _ => rw [hF3 (lo + 1) (by omega) (by omega) (by omega),
                  hF2 (lo + 1) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 1 (by omega)
      | 3, _ => rw [hF3 (lo + 3) (by omega) (by omega) (by omega),
                  hF2 (lo + 3) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 3 (by omega)
      | 4, _ => rw [hF3 (lo + 4) (by omega) (by omega) (by omega),
                  hF2 (lo + 4) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 4 (by omega)
      | 6, _ => rw [hF3 (lo + 6) (by omega) (by omega) (by omega),
                  hF2 (lo + 6) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 6 (by omega)
      | 7, _ => rw [hF3 (lo + 7) (by omega) (by omega) (by omega),
                  hF2 (lo + 7) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 7 (by omega)
    · intro q hqa hqb hqo hqr
      rw [hF3 q hqa hqo (by omega), hF2 q hqb hqo (by omega) (by omega),
        hF1 q hqa hqb (by omega) (by omega) (by omega)]
  · -- The other arm: the output is `a * a + a + b`.
    have hpcGE : s1.pc = base + 30 := by rw [hpc1, if_neg hlt]
    -- Square `a` into the output.
    rcases squareVar_effect p a out (lo + 2) (lo + 5) (base + 30) (base + 33)
      (base + 35) (base + 41) (by omega) (by omega) (by omega)
      (fun hc => hao hc) (by omega) (by omega)
      (hg 30 _ rfl) (hg 31 _ rfl) (hg 32 _ rfl) (hg 33 _ rfl) (hg 34 _ rfl)
      (hg 35 _ rfl) (hg 36 _ rfl) (hg 37 _ rfl) (hg 38 _ rfl) (hg 39 _ rfl) (hg 40 _ rfl)
      s1 hpcGE (hz1 5 (by omega)) (hz1 2 (by omega)) with
      ⟨s2, hr2, hpc2, hA2, hV2, hSc2, hO2, hF2⟩
    -- Add `a` again, then `b`.
    rcases copyBack_effect p a out (lo + 5) (base + 41) (base + 44) (base + 46)
      (fun hc => hao hc) (by omega) (by omega)
      (hg 41 _ rfl) (hg 42 _ rfl) (hg 43 _ rfl) (hg 44 _ rfl) (hg 45 _ rfl)
      s2 hpc2 hSc2 with ⟨s3, hr3, hpc3, hA3, hO3, hSc3, hF3⟩
    rcases copyBack_effect p b out (lo + 5) (base + 46) (base + 49) exit
      (fun hc => hbo hc) (by omega) (by omega)
      (hg 46 _ rfl) (hg 47 _ rfl) (hg 48 _ rfl) (hg 49 _ rfl) (hg 50 _ rfl)
      s3 hpc3 hSc3 with ⟨s4, hr4, hpc4, hB4, hO4, hSc4, hF4⟩
    refine ⟨s4, reaches_trans hr1 (reaches_trans hr2 (reaches_trans hr3 hr4)),
      hpc4, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hF4 a (fun hc => hab hc) (fun hc => hao hc) (by omega), hA3, hA2, hA1]
    · rw [hB4, hF3 b (fun hc => hab hc.symm) (fun hc => hbo hc) (by omega),
        hF2 b (by omega) (fun hc => hbo hc) (by omega) (by omega), hB1]
    · -- `a * a` from the squaring, then `a`, then `b`.
      rw [hO4, hO3, hO2, hout1, Nat.zero_add, hA2, hA1,
        hF3 b (fun hc => hab hc.symm) (fun hc => hbo hc) (by omega),
        hF2 b (by omega) (fun hc => hbo hc) (by omega) (by omega), hB1,
        Nat.pair, if_neg hlt]
    · intro j hj
      match j, hj with
      | 5, _ => exact hSc4
      | 2, _ => rw [hF4 (lo + 2) (by omega) (by omega) (by omega),
                  hF3 (lo + 2) (by omega) (by omega) (by omega)]
                exact hV2
      | 0, _ => rw [Nat.add_zero, hF4 lo (by omega) (by omega) (by omega),
                  hF3 lo (by omega) (by omega) (by omega),
                  hF2 lo (by omega) (by omega) (by omega) (by omega)]
                simpa only [Nat.add_zero] using hz1 0 (by omega)
      | 1, _ => rw [hF4 (lo + 1) (by omega) (by omega) (by omega),
                  hF3 (lo + 1) (by omega) (by omega) (by omega),
                  hF2 (lo + 1) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 1 (by omega)
      | 3, _ => rw [hF4 (lo + 3) (by omega) (by omega) (by omega),
                  hF3 (lo + 3) (by omega) (by omega) (by omega),
                  hF2 (lo + 3) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 3 (by omega)
      | 4, _ => rw [hF4 (lo + 4) (by omega) (by omega) (by omega),
                  hF3 (lo + 4) (by omega) (by omega) (by omega),
                  hF2 (lo + 4) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 4 (by omega)
      | 6, _ => rw [hF4 (lo + 6) (by omega) (by omega) (by omega),
                  hF3 (lo + 6) (by omega) (by omega) (by omega),
                  hF2 (lo + 6) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 6 (by omega)
      | 7, _ => rw [hF4 (lo + 7) (by omega) (by omega) (by omega),
                  hF3 (lo + 7) (by omega) (by omega) (by omega),
                  hF2 (lo + 7) (by omega) (by omega) (by omega) (by omega)]
                exact hz1 7 (by omega)
    · intro q hqa hqb hqo hqr
      rw [hF4 q hqb hqo (by omega), hF3 q hqa hqo (by omega),
        hF2 q hqa hqo (by omega) (by omega),
        hF1 q hqa hqb (by omega) (by omega) (by omega)]

end Register

end LeanBF
