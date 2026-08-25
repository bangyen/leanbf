/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Arith

/-!
# Discharging the Primitive Recursive Cases

The builders for the constructors of `Nat.Primrec` that need the arithmetic
fragments. `zero`, `succ` and `comp` are already in `Theory.Universal.Builder`,
which the fragments themselves import; these are the ones that go the other
way, so they live above both.

`builds_pair` runs both sub-builders on the same input, which is what the
calling convention's promise to preserve the input register buys: the second
one reads exactly what the first one did. Their two results are held in the
two registers just below the scratch the sub-builders see, so neither
disturbs the other's, and the pairing fragment reads both.

`prec` is the only case whose sub-builder runs more than once. `Computes` is
a statement about every state, and the builder is parametric in its base, so
the step function's fragment is placed once at a fixed address inside the
loop body and applied afresh on each pass. Nothing needs to be relocated; the
invariant's job is only to re-establish that fragment's entry conditions,
which is what the body's clears are for. Leaving out the clear of the
accumulator, in particular, hands the step function an output register that
is not empty.

`left` and `right` share one fragment. `Nat.unpair` produces both halves at
once, and the builder interface names only one output, so the unwanted half
is sent to the bottom of the caller's scratch region and cleared afterwards.
That is the same move `builds_comp` makes with its midpoint: a register the
caller has already guaranteed is clear can carry a value, as long as the
fragment puts it back.

## Main definitions

* `precBodyPre`: The body's instructions before the step function's fragment.
* `precBodyPost`: The body's instructions after it.
* `precPost`: The instructions after the loop.

## Theorems

* `builds_left`: The first half of the unpairing is computable.
* `builds_right`: The second half of the unpairing is computable.
* `builds_pair`: The pairing of two computable functions is computable.
* `precBodyPre_effect`: The body's prelude assembles the step's argument.
* `precBodyPost_effect`: The body's postlude counts up and returns.
* `precBody_effect`: One iteration advances the recursion by one step.
-/

namespace LeanBF

namespace Register

/-- The first half of the unpairing. The second half lands in `lo`, the
    bottom of the caller's scratch, and a trailing clear empties it. -/
theorem builds_left : Builds (fun n => n.unpair.1) := by
  intro inR outR lo hio hin hout base
  refine ⟨lo + 17, unpairFrag inR outR lo (lo + 1) base (base + 93) ++
    [Instruction.jzdec lo (base + 94) (base + 93)], by omega, fun p hemb s hpc hout0 hzero => ?_⟩
  have hembU := embeddedAt_append_left p base _ _ hemb
  have hclrSlot : p[base + 93]? = some (Instruction.jzdec lo (base + 94) (base + 93)) := by
    have h := embeddedAt_append_right p base _ _ hemb 0 (by
      simp only [List.length_cons, List.length_nil]
      omega)
    rwa [unpairFrag_length, Nat.add_zero] at h
  rcases unpairVar_effect p inR outR lo (lo + 1) base (base + 93)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hembU
    s hpc hout0 (hzero lo (le_refl _) (by omega))
    (fun j hj => hzero (lo + 1 + j) (by omega) (by omega)) with
    ⟨s1, hr1, hpc1, hN1, hO1, hL1, hZ1, hF1⟩
  refine ⟨{ pc := base + 94, regs := fun i => if i = lo then 0 else s1.regs i },
    reaches_trans hr1 (clear_reaches p lo (base + 93) (base + 94) hclrSlot _ s1 hpc1 rfl),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, unpairFrag_length, List.length_cons, List.length_nil]
  · simp only []
    rw [if_neg (by omega : outR ≠ lo), hO1]
  · simp only []
    rw [if_neg (by omega : inR ≠ lo), hN1]
  · intro r hlor hrhi
    simp only []
    by_cases hrl : r = lo
    · rw [if_pos hrl]
    · rw [if_neg hrl]
      have := hZ1 (r - (lo + 1)) (by omega)
      rwa [show lo + 1 + (r - (lo + 1)) = r by omega] at this
  · intro q hqo hqlohi
    simp only []
    rw [if_neg (by omega : q ≠ lo)]
    by_cases hqi : q = inR
    · rw [hqi, hN1]
    · exact hF1 q hqi hqo (by omega) (by omega)

/-- The second half of the unpairing, the mirror of `builds_left`: the first
    half is what goes to `lo` and gets cleared. -/
theorem builds_right : Builds (fun n => n.unpair.2) := by
  intro inR outR lo hio hin hout base
  refine ⟨lo + 17, unpairFrag inR lo outR (lo + 1) base (base + 93) ++
    [Instruction.jzdec lo (base + 94) (base + 93)], by omega, fun p hemb s hpc hout0 hzero => ?_⟩
  have hembU := embeddedAt_append_left p base _ _ hemb
  have hclrSlot : p[base + 93]? = some (Instruction.jzdec lo (base + 94) (base + 93)) := by
    have h := embeddedAt_append_right p base _ _ hemb 0 (by
      simp only [List.length_cons, List.length_nil]
      omega)
    rwa [unpairFrag_length, Nat.add_zero] at h
  rcases unpairVar_effect p inR lo outR (lo + 1) base (base + 93)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hembU
    s hpc (hzero lo (le_refl _) (by omega)) hout0
    (fun j hj => hzero (lo + 1 + j) (by omega) (by omega)) with
    ⟨s1, hr1, hpc1, hN1, hL1, hO1, hZ1, hF1⟩
  refine ⟨{ pc := base + 94, regs := fun i => if i = lo then 0 else s1.regs i },
    reaches_trans hr1 (clear_reaches p lo (base + 93) (base + 94) hclrSlot _ s1 hpc1 rfl),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, unpairFrag_length, List.length_cons, List.length_nil]
  · simp only []
    rw [if_neg (by omega : outR ≠ lo), hO1]
  · simp only []
    rw [if_neg (by omega : inR ≠ lo), hN1]
  · intro r hlor hrhi
    simp only []
    by_cases hrl : r = lo
    · rw [if_pos hrl]
    · rw [if_neg hrl]
      have := hZ1 (r - (lo + 1)) (by omega)
      rwa [show lo + 1 + (r - (lo + 1)) = r by omega] at this
  · intro q hqo hqlohi
    simp only []
    rw [if_neg (by omega : q ≠ lo)]
    by_cases hqi : q = inR
    · rw [hqi, hN1]
    · exact hF1 q hqi (by omega) hqo (by omega)

/-- Pairing two computable functions. Both sub-builders run on the same
    input, since each preserves the input register, and their results wait in
    the two registers below the scratch region they were given. -/
theorem builds_pair (f g : Nat → Nat) (hf : Builds f) (hg : Builds g) :
    Builds (fun n => Nat.pair (f n) (g n)) := by
  intro inR outR lo hio hin hout base
  rcases hf inR lo (lo + 2) (by omega) (by omega) (by omega) base with ⟨hiF, fragF, hloF, hF⟩
  rcases hg inR (lo + 1) (lo + 2) (by omega) (by omega) (by omega)
    (base + fragF.length) with ⟨hiG, fragG, hloG, hG⟩
  -- Addresses of the three stages that follow the two sub-fragments.
  set pb : Nat := base + fragF.length + fragG.length with hpb
  refine ⟨max (max hiF hiG) (lo + 10), fragF ++ fragG ++
    pairFrag lo (lo + 1) outR (lo + 2) pb (pb + 51) ++
    [Instruction.jzdec lo (pb + 52) (pb + 51),
     Instruction.jzdec (lo + 1) (pb + 53) (pb + 52)],
    by omega, fun p hemb s hpc hout0 hzero => ?_⟩
  have hembFG := embeddedAt_append_left p base _ _
    (embeddedAt_append_left p base _ _ hemb)
  have hembF := hF p (embeddedAt_append_left p base fragF fragG hembFG)
  have hembG := hG p (embeddedAt_append_right p base fragF fragG hembFG)
  have hembP := embeddedAt_append_right p base _ _ (embeddedAt_append_left p base _ _ hemb)
  have hembC := embeddedAt_append_right p base _ _ hemb
  have hlenFG : (fragF ++ fragG).length = fragF.length + fragG.length := List.length_append
  have hembP' : EmbeddedAt p pb (pairFrag lo (lo + 1) outR (lo + 2) pb (pb + 51)) := by
    have heq : base + (fragF ++ fragG).length = pb := by
      rw [hlenFG, hpb, Nat.add_assoc]
    rwa [heq] at hembP
  have hgc := embeddedAt_get p _ _ hembC
  have hlenP : (fragF ++ fragG ++ pairFrag lo (lo + 1) outR (lo + 2) pb (pb + 51)).length
      = fragF.length + fragG.length + 51 := by
    rw [List.length_append, hlenFG, pairFrag_length]
  have hc1 : p[pb + 51]? = some (Instruction.jzdec lo (pb + 52) (pb + 51)) := by
    have h := hgc 0 _ rfl
    rwa [hlenP, hpb, Nat.add_zero, ← Nat.add_assoc, ← Nat.add_assoc] at h
  have hc2 : p[pb + 52]? = some (Instruction.jzdec (lo + 1) (pb + 53) (pb + 52)) := by
    have h := hgc 1 _ rfl
    rwa [hlenP, hpb, ← Nat.add_assoc, ← Nat.add_assoc] at h
  -- Widen both sub-fragments to the region the pairing needs.
  have hFw := computes_mono_hi p base _ inR lo (lo + 2) hiF (max (max hiF hiG) (lo + 10)) f
    (by omega) (by omega) hembF
  have hGw := computes_mono_hi p _ _ inR (lo + 1) (lo + 2) hiG (max (max hiF hiG) (lo + 10)) g
    (by omega) (by omega) hembG
  -- Run `f`, then `g` on the same input, which `f` left alone.
  rcases hFw s hpc (hzero lo (le_refl _) (by omega))
    (fun r h1 h2 => hzero r (by omega) h2) with
    ⟨s1, hr1, hpc1, hV1, hI1, hZ1, hFr1⟩
  rcases hGw s1 hpc1
    (by rw [hFr1 (lo + 1) (by omega) (by omega)]; exact hzero (lo + 1) (by omega) (by omega))
    hZ1 with ⟨s2, hr2, hpc2, hV2, hI2, hZ2, hFr2⟩
  -- The pairing reads both results.
  rcases pairVar_effect p lo (lo + 1) outR (lo + 2) pb (pb + 51)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hembP'
    s2 hpc2
    (by
      rw [hFr2 outR (by omega) (by omega), hFr1 outR (by omega) (by omega)]
      exact hout0)
    (fun j hj => hZ2 (lo + 2 + j) (by omega) (by omega)) with
    ⟨s3, hr3, hpc3, hA3, hB3, hO3, hZ3, hFr3⟩
  -- Clear the two results, restoring the caller's scratch contract.
  have hclr1 := clear_reaches p lo (pb + 51) (pb + 52) hc1 (s3.regs lo) s3 hpc3 rfl
  set s4 : State := { pc := pb + 52, regs := fun i => if i = lo then 0 else s3.regs i } with hs4
  have hclr2 := clear_reaches p (lo + 1) (pb + 52) (pb + 53) hc2 (s4.regs (lo + 1)) s4 rfl rfl
  refine ⟨_, reaches_trans hr1 (reaches_trans hr2 (reaches_trans hr3
    (reaches_trans hclr1 hclr2))), ?_, ?_, ?_, ?_, ?_⟩
  · -- The exit is just past the whole fragment.
    simp only [List.length_append, hlenFG, pairFrag_length, List.length_cons, List.length_nil,
      hpb]
    omega
  · -- The output is the pairing of the two results.
    simp only [if_neg (by omega : outR ≠ lo + 1), hs4, if_neg (by omega : outR ≠ lo)]
    rw [hO3, hV2, hI1, hFr2 lo (by omega) (by omega), hV1]
  · simp only [if_neg (by omega : inR ≠ lo + 1), hs4, if_neg (by omega : inR ≠ lo)]
    rw [hFr3 inR (by omega) (by omega) (by omega) (by omega), hI2, hI1]
  · intro r hlor hrhi
    by_cases hr1' : r = lo + 1
    · simp only [hr1', if_true]
    · simp only [if_neg hr1', hs4]
      by_cases hr0 : r = lo
      · rw [if_pos hr0]
      · rw [if_neg hr0]
        by_cases hrlow : r < lo + 10
        · have := hZ3 (r - (lo + 2)) (by omega)
          rwa [show lo + 2 + (r - (lo + 2)) = r by omega] at this
        · -- Above the pairing's block: the sub-fragments left it clear and
          -- the pairing's frame carries that through.
          rw [hFr3 r hr0 hr1' (by omega) (by omega)]
          exact hZ2 r (by omega) hrhi
  · intro q hqo hqlohi
    simp only [if_neg (by omega : q ≠ lo + 1), hs4, if_neg (by omega : q ≠ lo)]
    by_cases hqi : q = inR
    · rw [hqi, hFr3 inR (by omega) (by omega) (by omega) (by omega), hI2, hI1]
    · rw [hFr3 q (by omega) (by omega) hqo (by omega),
        hFr2 q (by omega) (by omega), hFr1 q (by omega) (by omega)]

/-- The body's prelude: assemble `pair z (pair y acc)` in `lo + 4`, clearing
    the accumulator and the inner pair on the way so the step function's
    fragment starts from the conditions it requires. Laid out from `base`,
    with the two pairings at `base` and `base + 51`. -/
def precBodyPre (lo base : Nat) : Program :=
  pairFrag (lo + 2) (lo + 1) (lo + 3) (lo + 6) base (base + 51) ++
  pairFrag lo (lo + 3) (lo + 4) (lo + 6) (base + 51) (base + 102) ++
  [Instruction.jzdec (lo + 1) (base + 103) (base + 102),
   Instruction.jzdec (lo + 3) (base + 104) (base + 103)]

/-- The body's postlude: clear the assembled argument, count the iteration,
    and return to the loop head. The return is a test of a register the
    invariant keeps empty, since the instruction set has no plain jump. -/
def precBodyPost (lo base head : Nat) : Program :=
  [Instruction.jzdec (lo + 4) (base + 1) base,
   Instruction.inc (lo + 2) (base + 2),
   Instruction.jzdec (lo + 6) head head]

/-- After the loop: move the accumulator to the output, then empty the two
    registers still holding values. The iteration counter ends at the number
    of iterations, not at zero, so it needs clearing too. -/
def precPost (outR lo base exit : Nat) : Program :=
  [Instruction.jzdec (lo + 1) (base + 2) (base + 1),
   Instruction.inc outR base,
   Instruction.jzdec lo (base + 3) (base + 2),
   Instruction.jzdec (lo + 2) exit (base + 3)]

/-- The prelude assembles `pair z (pair y acc)` into `lo + 4` and leaves the
    accumulator and the inner pair empty, which is what the step function's
    fragment needs to run. -/
theorem precBodyPre_effect (p : Program) (lo base : Nat)
    (hemb : EmbeddedAt p base (precBodyPre lo base)) :
    ∀ (s : State), s.pc = base → s.regs (lo + 3) = 0 → s.regs (lo + 4) = 0 →
      (∀ j, j < 8 → s.regs (lo + 6 + j) = 0) →
      ∃ s', Reaches p s s' ∧ s'.pc = base + 104 ∧
        s'.regs lo = s.regs lo ∧ s'.regs (lo + 2) = s.regs (lo + 2) ∧
        s'.regs (lo + 1) = 0 ∧ s'.regs (lo + 3) = 0 ∧
        s'.regs (lo + 4) = Nat.pair (s.regs lo) (Nat.pair (s.regs (lo + 2)) (s.regs (lo + 1))) ∧
        (∀ j, j < 8 → s'.regs (lo + 6 + j) = 0) ∧
        ∀ q, q ≠ lo → q ≠ lo + 1 → q ≠ lo + 2 → q ≠ lo + 3 → q ≠ lo + 4 →
          (q < lo + 6 ∨ lo + 6 + 8 ≤ q) → s'.regs q = s.regs q := by
  intro s hpc h30 h40 hz
  have hemb1 := embeddedAt_append_left p base _ _ (embeddedAt_append_left p base _ _ hemb)
  have hemb2raw := embeddedAt_append_right p base _ _ (embeddedAt_append_left p base _ _ hemb)
  have hemb2 : EmbeddedAt p (base + 51)
      (pairFrag lo (lo + 3) (lo + 4) (lo + 6) (base + 51) (base + 102)) := by
    rwa [pairFrag_length] at hemb2raw
  have hgc := embeddedAt_get p _ _ (embeddedAt_append_right p base _ _ hemb)
  have hlen2 : (pairFrag (lo + 2) (lo + 1) (lo + 3) (lo + 6) base (base + 51) ++
      pairFrag lo (lo + 3) (lo + 4) (lo + 6) (base + 51) (base + 102)).length = 102 := by
    rw [List.length_append, pairFrag_length, pairFrag_length]
  have hc1 : p[base + 102]? = some (Instruction.jzdec (lo + 1) (base + 103) (base + 102)) := by
    have h := hgc 0 _ rfl
    rwa [hlen2, Nat.add_zero] at h
  have hc2 : p[base + 103]? = some (Instruction.jzdec (lo + 3) (base + 104) (base + 103)) := by
    have h := hgc 1 _ rfl
    rwa [hlen2] at h
  -- The inner pairing of the counter with the accumulator.
  rcases pairVar_effect p (lo + 2) (lo + 1) (lo + 3) (lo + 6) base (base + 51)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hemb1
    s hpc h30 hz with ⟨s1, hr1, hpc1, hY1, hA1, hU1, hZ1, hF1⟩
  -- Then the outer pairing with the first component.
  rcases pairVar_effect p lo (lo + 3) (lo + 4) (lo + 6) (base + 51) (base + 102)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hemb2
    s1 hpc1 (by rw [hF1 (lo + 4) (by omega) (by omega) (by omega) (by omega)]; exact h40)
    hZ1 with ⟨s2, hr2, hpc2, hZ2', hU2, hT2, hZ2, hF2⟩
  -- Clear the accumulator, then the inner pair.
  have hclr1 := clear_reaches p (lo + 1) (base + 102) (base + 103) hc1 (s2.regs (lo + 1)) s2
    hpc2 rfl
  set s3 : State :=
    { pc := base + 103, regs := fun i => if i = lo + 1 then 0 else s2.regs i } with hs3
  have hclr2 := clear_reaches p (lo + 3) (base + 103) (base + 104) hc2 (s3.regs (lo + 3)) s3
    rfl rfl
  refine ⟨_, reaches_trans hr1 (reaches_trans hr2 (reaches_trans hclr1 hclr2)),
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [if_neg (by omega : lo ≠ lo + 3), hs3, if_neg (by omega : lo ≠ lo + 1)]
    rw [hZ2', hF1 lo (by omega) (by omega) (by omega) (by omega)]
  · simp only [if_neg (by omega : lo + 2 ≠ lo + 3), hs3, if_neg (by omega : lo + 2 ≠ lo + 1)]
    rw [hF2 (lo + 2) (by omega) (by omega) (by omega) (by omega), hY1]
  · simp only [if_neg (by omega : lo + 1 ≠ lo + 3), hs3, if_true]
  · simp only [if_true]
  · -- The assembled argument.
    simp only [if_neg (by omega : lo + 4 ≠ lo + 3), hs3, if_neg (by omega : lo + 4 ≠ lo + 1)]
    rw [hT2, hU1, hF1 lo (by omega) (by omega) (by omega) (by omega)]
  · intro j hj
    simp only [if_neg (by omega : lo + 6 + j ≠ lo + 3), hs3,
      if_neg (by omega : lo + 6 + j ≠ lo + 1)]
    exact hZ2 j hj
  · intro q hq0 hq1 hq2 hq3 hq4 hqr
    simp only [if_neg hq3, hs3, if_neg hq1]
    rw [hF2 q hq0 hq3 hq4 (by omega), hF1 q hq2 hq1 hq3 (by omega)]

/-- The postlude: clear the argument the step function consumed, count the
    iteration, and return to the loop head. The return tests a register the
    invariant keeps empty, which is how a machine without a plain jump makes
    an unconditional one. -/
theorem precBodyPost_effect (p : Program) (lo base head : Nat)
    (hemb : EmbeddedAt p base (precBodyPost lo base head)) :
    ∀ (s : State), s.pc = base → s.regs (lo + 6) = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = head ∧ s'.regs (lo + 4) = 0 ∧
        s'.regs (lo + 2) = s.regs (lo + 2) + 1 ∧
        ∀ q, q ≠ lo + 4 → q ≠ lo + 2 → s'.regs q = s.regs q := by
  intro s hpc h60
  have hg := embeddedAt_get p base _ hemb
  -- Clear the argument.
  have hclr := clear_reaches p (lo + 4) base (base + 1)
    (by simpa only [Nat.add_zero] using hg 0 _ rfl) (s.regs (lo + 4)) s hpc rfl
  set s1 : State := { pc := base + 1, regs := fun i => if i = lo + 4 then 0 else s.regs i }
    with hs1
  -- Count the iteration.
  have hstep : step p s1 = some { setReg s1 (lo + 2) (s1.regs (lo + 2) + 1) with
      pc := base + 2 } := by
    simp only [step, hs1, hg 1 _ rfl, setReg]
  set s2 : State := { setReg s1 (lo + 2) (s1.regs (lo + 2) + 1) with pc := base + 2 } with hs2
  -- Return to the head by testing a register the invariant keeps empty.
  have hzero6 : s2.regs (lo + 6) = 0 := by
    simp only [hs2, setReg, if_neg (by omega : lo + 6 ≠ lo + 2), hs1,
      if_neg (by omega : lo + 6 ≠ lo + 4)]
    exact h60
  have hjump : step p s2 = some { s2 with pc := head } := by
    rw [step, hs2]
    simp only [hg 2 _ rfl]
    rw [show (setReg s1 (lo + 2) (s1.regs (lo + 2) + 1)).regs (lo + 6) = 0 from hzero6]
    simp only [if_pos]
  refine ⟨{ s2 with pc := head }, reaches_trans hclr (Reaches.step _ _ _ hstep
    (Reaches.step _ _ _ hjump (Reaches.refl _))), rfl, ?_, ?_, ?_⟩
  · simp only [hs2, setReg, if_neg (by omega : lo + 4 ≠ lo + 2), hs1, if_true]
  · simp only [hs2, setReg, if_true, hs1, if_neg (by omega : lo + 2 ≠ lo + 4)]
  · intro q hq4 hq2
    simp only [hs2, setReg, if_neg hq2, hs1, if_neg hq4]

/-- One iteration of the primitive recursion. The step function's fragment
    is taken as a hypothesis rather than a builder, because the assembly above
    places it once at a fixed address and applies it afresh on every pass. -/
theorem precBody_effect (p : Program) (lo hd hi gl : Nat) (g : Nat → Nat)
    (hhi : lo + 22 ≤ hi)
    (hembPre : EmbeddedAt p (hd + 1) (precBodyPre lo (hd + 1)))
    (hg : Computes p (hd + 105) (hd + 105 + gl) (lo + 4) (lo + 1) (lo + 6) hi g)
    (hembPost : EmbeddedAt p (hd + 105 + gl) (precBodyPost lo (hd + 105 + gl) hd)) :
    ∀ (s : State), s.pc = hd + 1 → s.regs (lo + 3) = 0 → s.regs (lo + 4) = 0 →
      (∀ r, lo + 6 ≤ r → r < hi → s.regs r = 0) →
      ∃ s', Reaches p s s' ∧ s'.pc = hd ∧
        s'.regs lo = s.regs lo ∧ s'.regs (lo + 2) = s.regs (lo + 2) + 1 ∧
        s'.regs (lo + 1) = g (Nat.pair (s.regs lo)
          (Nat.pair (s.regs (lo + 2)) (s.regs (lo + 1)))) ∧
        s'.regs (lo + 3) = 0 ∧ s'.regs (lo + 4) = 0 ∧
        (∀ r, lo + 6 ≤ r → r < hi → s'.regs r = 0) ∧
        ∀ q, q < lo ∨ lo + 5 = q ∨ hi ≤ q → s'.regs q = s.regs q := by
  intro s hpc h30 h40 hz
  -- Assemble the argument for the step function.
  rcases precBodyPre_effect p lo (hd + 1) hembPre s hpc h30 h40
    (fun j hj => hz (lo + 6 + j) (by omega) (by omega)) with
    ⟨s1, hr1, hpc1, hZ1, hY1, hA1, hU1, hT1, hB1, hF1⟩
  -- Apply the step function to it.
  rcases hg s1 (by omega) hA1
    (fun r hr1' hr2' => by
      by_cases hlow : r < lo + 14
      · have := hB1 (r - (lo + 6)) (by omega)
        rwa [show lo + 6 + (r - (lo + 6)) = r by omega] at this
      · rw [hF1 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hz r hr1' hr2') with
    ⟨s2, hr2, hpc2, hV2, hI2, hZ2, hF2⟩
  -- Count the iteration and return to the head.
  rcases precBodyPost_effect p lo (hd + 105 + gl) hd hembPost s2 hpc2
    (hZ2 (lo + 6) (by omega) (by omega)) with ⟨s3, hr3, hpc3, hT3, hY3, hF3⟩
  refine ⟨s3, reaches_trans hr1 (reaches_trans hr2 hr3), hpc3, ?_, ?_, ?_, ?_, hT3, ?_, ?_⟩
  · rw [hF3 lo (by omega) (by omega), hF2 lo (by omega) (by omega), hZ1]
  · rw [hY3, hF2 (lo + 2) (by omega) (by omega), hY1]
  · -- The step function's answer, on the argument the prelude built.
    rw [hF3 (lo + 1) (by omega) (by omega), hV2, hT1]
  · rw [hF3 (lo + 3) (by omega) (by omega), hF2 (lo + 3) (by omega) (by omega), hU1]
  · intro r hr1' hr2'
    rw [hF3 r (by omega) (by omega)]
    exact hZ2 r hr1' hr2'
  · intro q hq
    rw [hF3 q (by omega) (by omega), hF2 q (by omega) (by omega),
      hF1 q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

end Register

end LeanBF
