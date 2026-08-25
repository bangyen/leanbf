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

`left` and `right` share one fragment. `Nat.unpair` produces both halves at
once, and the builder interface names only one output, so the unwanted half
is sent to the bottom of the caller's scratch region and cleared afterwards.
That is the same move `builds_comp` makes with its midpoint: a register the
caller has already guaranteed is clear can carry a value, as long as the
fragment puts it back.

## Theorems

* `builds_left`: The first half of the unpairing is computable.
* `builds_right`: The second half of the unpairing is computable.
* `builds_pair`: The pairing of two computable functions is computable.
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

end Register

end LeanBF
