/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Transfer

/-!
# Truncated Subtraction

Subtracting one register from another, saturating at zero.

The interesting slot is the loop body, a single `jzdec` on the minuend whose
two exits are the *same* address. When the minuend is positive it decrements
and returns to the loop head; when it is already zero it jumps to the loop
head without decrementing. Saturation therefore costs no branch at all —
`Nat` subtraction's own truncation is exactly what the instruction does when
it cannot decrement.

The invariant carries the bound `m ≤ b0` for the same reason `MulInv` does:
`b0 - m` stops moving once the counter passes its starting value, so without
the bound the step from `m + 1` to `m` no longer removes a unit.

`cmpBranch_effect` follows `div_reaches` in answering with an address rather
than a value: there is no register holding a truth value at the end, only the
program counter, which lands on one exit or the other. That is the only form
a conditional can take here, and it is what the two-armed constructions above
`Nat.pair` and `Nat.unpair` consume.

Its `jzdec` test decrements the scratch it reads, so the strictly-less arm
enters its clear loop one unit down. The value is never stated, only that
both arms leave the scratch empty, which is what keeps the fragment usable
by a caller that demands a clean region.

## Main definitions

* `SubInv`: The subtraction loop's invariant on the register file.

## Theorems

* `subInv_congr`: The invariant ignores the counter register.
* `sub_body_effect`: One iteration removes a unit, saturating at zero.
* `subLoop_effect`: The loop subtracts a counter from a register.
* `subVar_effect`: One register is subtracted from another, both preserved.
* `cmpBranch_effect`: A comparison branches on which register is larger.
-/

namespace LeanBF

namespace Register

/-- The subtraction loop's invariant, indexed by iterations remaining: the
    target holds the minuend less however many units have been removed. -/
def SubInv (t : Nat) (a0 b0 : Nat) (m : Nat) (f : Nat → Nat) : Prop :=
  m ≤ b0 ∧ f t = a0 - (b0 - m)

theorem subInv_congr (t a0 b0 c : Nat) (htc : t ≠ c) :
    ∀ (m : Nat) (f g : Nat → Nat), (∀ i, i ≠ c → f i = g i) →
      SubInv t a0 b0 m f → SubInv t a0 b0 m g := by
  intro m f g hfg hI
  exact ⟨hI.1, by rw [← hfg t htc]; exact hI.2⟩

/-- One iteration: the single `jzdec` removes a unit from the target, or
    leaves it at zero when there is nothing left to remove. Both of its
    exits are the loop head, so the two cases rejoin immediately. -/
theorem sub_body_effect (p : Program) (t c base : Nat) (htc : t ≠ c)
    (a0 b0 : Nat)
    (hbody : p[base + 1]? = some (Instruction.jzdec t base base)) :
    ∀ (m : Nat) (s : State), s.pc = base + 1 → s.regs c = m →
      SubInv t a0 b0 (m + 1) s.regs →
      ∃ s', Reaches p s s' ∧ s'.pc = base ∧ s'.regs c = m ∧
        SubInv t a0 b0 m s'.regs ∧ ∀ r, r ≠ t → s'.regs r = s.regs r := by
  intro m s hpc hc hI
  have hmb : m + 1 ≤ b0 := hI.1
  have hsplit : b0 - m = (b0 - (m + 1)) + 1 := by omega
  by_cases hz : s.regs t = 0
  · -- Already saturated: the jump leaves every register alone.
    have hstep : step p s = some { s with pc := base } := by
      simp only [step, hpc, hbody, hz, if_pos]
    refine ⟨{ s with pc := base }, Reaches.step s _ _ hstep (Reaches.refl _), rfl, hc,
      ⟨by omega, ?_⟩, fun r _ => rfl⟩
    change s.regs t = a0 - (b0 - m)
    rw [hI.2] at hz ⊢
    omega
  · -- A unit comes off the target, matching the extra unit of the subtrahend.
    have hstep : step p s = some { setReg s t (s.regs t - 1) with pc := base } := by
      simp only [step, hpc, hbody, if_neg hz]
    refine ⟨{ setReg s t (s.regs t - 1) with pc := base },
      Reaches.step s _ _ hstep (Reaches.refl _), rfl, ?_, ⟨by omega, ?_⟩, ?_⟩
    · change (if c = t then s.regs t - 1 else s.regs c) = m
      rw [if_neg (fun hcc => htc hcc.symm)]
      exact hc
    · change (if t = t then s.regs t - 1 else s.regs t) = a0 - (b0 - m)
      rw [if_pos rfl, hI.2]
      omega
    · intro r hrt
      change (if r = t then s.regs t - 1 else s.regs r) = s.regs r
      rw [if_neg hrt]

/-- The loop subtracts the counter from the target, saturating at zero. The
    counter is consumed. -/
theorem subLoop_effect (p : Program) (t c base exit : Nat) (htc : t ≠ c)
    (hloop : p[base]? = some (Instruction.jzdec c exit (base + 1)))
    (hbody : p[base + 1]? = some (Instruction.jzdec t base base)) :
    ∀ (s : State), s.pc = base →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs c = 0 ∧
        s'.regs t = s.regs t - s.regs c ∧ ∀ r, r ≠ t → r ≠ c → s'.regs r = s.regs r := by
  intro s hpc
  -- The invariant also carries the frame, since `iterate_inv` threads only it.
  rcases iterate_inv p c base exit
    (fun m f => SubInv t (s.regs t) (s.regs c) m f ∧ ∀ r, r ≠ t → r ≠ c → f r = s.regs r)
    (fun m f g hfg hI => ⟨subInv_congr t (s.regs t) (s.regs c) c htc m f g hfg hI.1,
      fun r hrt hrc => by rw [← hfg r hrc]; exact hI.2 r hrt hrc⟩)
    hloop
    (fun m s1 hpc1 hc1 hI1 => by
      rcases sub_body_effect p t c base htc (s.regs t) (s.regs c) hbody m s1 hpc1 hc1 hI1.1 with
        ⟨s2, hr2, hpc2, hc2, hI2, hfr2⟩
      exact ⟨s2, hr2, hpc2, hc2, hI2, fun r hrt hrc => by
        rw [hfr2 r hrt]; exact hI1.2 r hrt hrc⟩)
    (s.regs c) s hpc rfl
    ⟨⟨le_refl _, by rw [Nat.sub_self, Nat.sub_zero]⟩, fun r _ _ => rfl⟩ with
    ⟨s', hr, hpc', hc', hI'⟩
  exact ⟨s', hr, hpc', hc', by rw [hI'.1.2, Nat.sub_zero], hI'.2⟩

/-- Truncated subtraction of two registers into a third, with both operands
    preserved. The minuend is copied into the target and the subtrahend into
    a counter, so the destructive loop consumes only the copies. -/
theorem subVar_effect (p : Program) (a b t c sc base m1 m2 m3 loop exit : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (hbc : b ≠ c) (hbsc : b ≠ sc) (hcsc : c ≠ sc)
    (hab : a ≠ b) (hac : a ≠ c) (hbt : b ≠ t) (htc : t ≠ c)
    (ha0 : p[base]? = some (Instruction.jzdec a m1 (base + 1)))
    (ha1 : p[base + 1]? = some (Instruction.inc t (base + 2)))
    (ha2 : p[base + 2]? = some (Instruction.inc sc base))
    (hr0 : p[m1]? = some (Instruction.jzdec sc m2 (m1 + 1)))
    (hr1 : p[m1 + 1]? = some (Instruction.inc a m1))
    (hb0 : p[m2]? = some (Instruction.jzdec b m3 (m2 + 1)))
    (hb1 : p[m2 + 1]? = some (Instruction.inc c (m2 + 2)))
    (hb2 : p[m2 + 2]? = some (Instruction.inc sc m2))
    (hs0 : p[m3]? = some (Instruction.jzdec sc loop (m3 + 1)))
    (hs1 : p[m3 + 1]? = some (Instruction.inc b m3))
    (hloop : p[loop]? = some (Instruction.jzdec c exit (loop + 1)))
    (hbody : p[loop + 1]? = some (Instruction.jzdec t loop loop)) :
    ∀ (s : State), s.pc = base → s.regs sc = 0 → s.regs t = 0 → s.regs c = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs a = s.regs a ∧
        s'.regs b = s.regs b ∧ s'.regs sc = 0 ∧ s'.regs c = 0 ∧
        s'.regs t = s.regs a - s.regs b := by
  intro s hpc hsc ht0 hc0
  -- Copy the minuend into the target.
  rcases copyBack_effect p a t sc base m1 m2 hat hasc htsc ha0 ha1 ha2 hr0 hr1 s hpc hsc with
    ⟨s1, hr1', hpc1, hA1, hT1, hS1, hF1⟩
  -- Copy the subtrahend into the counter.
  rcases copyBack_effect p b c sc m2 m3 loop hbc hbsc hcsc hb0 hb1 hb2 hs0 hs1 s1 hpc1 hS1 with
    ⟨s2, hr2', hpc2, hB2, hC2, hS2, hF2⟩
  -- Drain the counter out of the target.
  rcases subLoop_effect p t c loop exit htc hloop hbody s2 hpc2 with
    ⟨s3, hr3', hpc3, hC3, hT3, hF3⟩
  -- Both operands sit outside the loop's two registers, so they survive it.
  have hA3 : s3.regs a = s.regs a := by
    rw [hF3 a (fun hc => hat hc) (fun hc => hac hc), hF2 a (fun hc => hab hc)
      (fun hc => hac hc) (fun hc => hasc hc), hA1]
  have hB3 : s3.regs b = s.regs b := by
    rw [hF3 b (fun hc => hbt hc) (fun hc => hbc hc), hB2]
    exact hF1 b (fun hc => hab hc.symm) (fun hc => hbt hc) (fun hc => hbsc hc)
  refine ⟨s3, reaches_trans hr1' (reaches_trans hr2' hr3'), hpc3, hA3, hB3, ?_, hC3, ?_⟩
  · rw [hF3 sc (fun hc => htsc hc.symm) (fun hc => hcsc hc.symm)]
    exact hS2
  · -- The target held a copy of the minuend; the counter held one of the
    -- subtrahend, and the loop drained the second out of the first.
    have hT2 : s2.regs t = s.regs a := by
      rw [hF2 t (fun hc => hbt hc.symm) (fun hc => htc hc) (fun hc => htsc hc), hT1, ht0,
        Nat.zero_add]
    have hC1 : s1.regs c = 0 := by
      rw [hF1 c (fun hc => hac hc.symm) (fun hc => htc hc.symm) (fun hc => hcsc hc)]
      exact hc0
    rw [hT3, hT2, hC2, hC1, Nat.zero_add,
      hF1 b (fun hc => hab hc.symm) (fun hc => hbt hc) (fun hc => hbsc hc)]

/-- Comparing two registers by where the machine ends up. Both operands are
    preserved and every scratch register is left clear, on both arms. -/
theorem cmpBranch_effect (p : Program) (a b t c sc base m1 m2 m3 loop test clr : Nat)
    (exitLT exitGE : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (hbc : b ≠ c) (hbsc : b ≠ sc) (hcsc : c ≠ sc)
    (hab : a ≠ b) (hac : a ≠ c) (hbt : b ≠ t) (htc : t ≠ c)
    (ha0 : p[base]? = some (Instruction.jzdec b m1 (base + 1)))
    (ha1 : p[base + 1]? = some (Instruction.inc t (base + 2)))
    (ha2 : p[base + 2]? = some (Instruction.inc sc base))
    (hr0 : p[m1]? = some (Instruction.jzdec sc m2 (m1 + 1)))
    (hr1 : p[m1 + 1]? = some (Instruction.inc b m1))
    (hb0 : p[m2]? = some (Instruction.jzdec a m3 (m2 + 1)))
    (hb1 : p[m2 + 1]? = some (Instruction.inc c (m2 + 2)))
    (hb2 : p[m2 + 2]? = some (Instruction.inc sc m2))
    (hs0 : p[m3]? = some (Instruction.jzdec sc loop (m3 + 1)))
    (hs1 : p[m3 + 1]? = some (Instruction.inc a m3))
    (hloop : p[loop]? = some (Instruction.jzdec c test (loop + 1)))
    (hbody : p[loop + 1]? = some (Instruction.jzdec t loop loop))
    (htest : p[test]? = some (Instruction.jzdec t exitGE clr))
    (hclr : p[clr]? = some (Instruction.jzdec t exitLT clr)) :
    ∀ (s : State), s.pc = base → s.regs sc = 0 → s.regs t = 0 → s.regs c = 0 →
      ∃ s', Reaches p s s' ∧ s'.regs a = s.regs a ∧ s'.regs b = s.regs b ∧
        s'.regs sc = 0 ∧ s'.regs c = 0 ∧ s'.regs t = 0 ∧
        s'.pc = if s.regs a < s.regs b then exitLT else exitGE := by
  intro s hpc hsc ht0 hc0
  -- The target holds `b - a`, which vanishes exactly when `b ≤ a`.
  rcases subVar_effect p b a t c sc base m1 m2 m3 loop test
    (fun hc => hbt hc) hbsc htsc hac hasc hcsc (fun hc => hab hc.symm) hbc
    (fun hc => hat hc) htc ha0 ha1 ha2 hr0 hr1 hb0 hb1 hb2 hs0 hs1 hloop hbody
    s hpc hsc ht0 hc0 with ⟨s1, hr1', hpc1, hB1, hA1, hS1, hC1, hT1⟩
  by_cases hlt : s.regs a < s.regs b
  · -- Strictly less: the test decrements, then the clear empties the rest.
    have hne : s1.regs t ≠ 0 := by rw [hT1]; omega
    have hstep : step p s1 = some { setReg s1 t (s1.regs t - 1) with pc := clr } := by
      simp only [step, hpc1, htest, if_neg hne]
    refine ⟨{ pc := exitLT, regs := fun i => if i = t then 0
        else (setReg s1 t (s1.regs t - 1)).regs i },
      reaches_trans hr1' (Reaches.step _ _ _ hstep
        (clear_reaches p t clr exitLT hclr _ _ rfl rfl)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (if a = t then 0 else (setReg s1 t (s1.regs t - 1)).regs a) = s.regs a
      rw [if_neg hat]
      change (if a = t then s1.regs t - 1 else s1.regs a) = s.regs a
      rw [if_neg hat, hA1]
    · change (if b = t then 0 else (setReg s1 t (s1.regs t - 1)).regs b) = s.regs b
      rw [if_neg hbt]
      change (if b = t then s1.regs t - 1 else s1.regs b) = s.regs b
      rw [if_neg hbt, hB1]
    · change (if sc = t then 0 else (setReg s1 t (s1.regs t - 1)).regs sc) = 0
      rw [if_neg (fun hc => htsc hc.symm)]
      change (if sc = t then s1.regs t - 1 else s1.regs sc) = 0
      rw [if_neg (fun hc => htsc hc.symm), hS1]
    · change (if c = t then 0 else (setReg s1 t (s1.regs t - 1)).regs c) = 0
      rw [if_neg (fun hc => htc hc.symm)]
      change (if c = t then s1.regs t - 1 else s1.regs c) = 0
      rw [if_neg (fun hc => htc hc.symm), hC1]
    · simp only [if_true]
    · simp only [if_pos hlt]
  · -- Not less: the target is already empty and the test jumps straight out.
    have hz : s1.regs t = 0 := by rw [hT1]; omega
    have hstep : step p s1 = some { s1 with pc := exitGE } := by
      simp only [step, hpc1, htest, hz, if_pos]
    exact ⟨{ s1 with pc := exitGE }, reaches_trans hr1' (Reaches.step _ _ _ hstep
      (Reaches.refl _)), hA1, hB1, hS1, hC1, hz, by simp only [if_neg hlt]⟩

end Register

end LeanBF
