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

`left` and `right` share one fragment. `Nat.unpair` produces both halves at
once, and the builder interface names only one output, so the unwanted half
is sent to the bottom of the caller's scratch region and cleared afterwards.
That is the same move `builds_comp` makes with its midpoint: a register the
caller has already guaranteed is clear can carry a value, as long as the
fragment puts it back.

## Theorems

* `builds_left`: The first half of the unpairing is computable.
* `builds_right`: The second half of the unpairing is computable.
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

end Register

end LeanBF
