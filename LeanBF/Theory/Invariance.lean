/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics
import LeanBF.Core.State
import LeanBF.Theory.Loop

/-!
# Run-Level Tape Invariance

Run-level generalizations of the single-step tape lemmas: a general
configuration invariant for `RunsTo`, and the fact that a run preserves every
tape cell above a bound on the pointer. These lift the cell-preservation
facts from individual instructions and windows to whole runs.

## Theorems

* `RunsTo_inv`: A configuration invariant preserved by every step holds at
  the final configuration.
* `step_preserves_tape_above`: A single step only modifies the current cell,
  so every cell above the pointer is preserved.
* `RunsTo_preserves_tape_above`: A run whose configurations keep the pointer
  below `n` preserves every cell above `n`.
* `runSeq_incVal_decVal_preserves`: Cells above the starting pointer are
  preserved by `[+ -]` run sequentially.
-/

namespace LeanBF

/-- An invariant for `RunsTo`: a property of configurations that holds
    initially and is preserved by every step holds at the final
    configuration. -/
theorem RunsTo_inv {cfg : Program × State} (s_final : State) (P : Program → State → Prop)
    (h : RunsTo cfg s_final) (hinit : P cfg.1 cfg.2)
    (hstep : ∀ {p : Program} {s : State}, P p s → ∀ {p' : Program} {s' : State},
      step p s = some (p', s') → P p' s') : P ([] : Program) s_final := by
  induction h with
  | halt s => exact hinit
  | step p s s' p' s_final hstep' hrest ih =>
      exact ih (hstep hinit hstep')

/-- A single step only modifies the current cell, so every cell above the
    pointer is preserved. -/
theorem step_preserves_tape_above (n : Int) (p : Program) (s : State) (p' : Program) (s' : State)
    (h : step p s = some (p', s')) (hptr : s.ptr < n) :
    ∀ i : Int, n < i → s'.tape i = s.tape i := by
  cases p with
  | nil => cases h
  | cons instr rest =>
      cases instr with
      | inc_ptr =>
          simp only [step] at h
          injection h with hpair
          injection hpair with hp' hs'
          intro i hi
          subst hs'
          rfl
      | dec_ptr =>
          simp only [step] at h
          injection h with hpair
          injection hpair with hp' hs'
          intro i hi
          subst hs'
          rfl
      | inc_val =>
          simp only [step] at h
          injection h with hpair
          injection hpair with hp' hs'
          intro i hi
          subst hs'
          simp only [State.incVal, State.modifyCell, if_neg (by omega : ¬ i = s.ptr)]
      | dec_val =>
          simp only [step] at h
          injection h with hpair
          injection hpair with hp' hs'
          intro i hi
          subst hs'
          simp only [State.decVal, State.modifyCell, if_neg (by omega : ¬ i = s.ptr)]
      | read =>
          cases hs : s.input with
          | nil =>
              simp only [step, hs] at h
              injection h with hpair
              injection hpair with hp' hs'
              intro i hi
              subst hs'
              simp only [if_neg (by omega : ¬ i = s.ptr)]
          | cons x xs =>
              simp only [step, hs] at h
              injection h with hpair
              injection hpair with hp' hs'
              intro i hi
              subst hs'
              simp only [if_neg (by omega : ¬ i = s.ptr)]
      | write =>
          simp only [step] at h
          injection h with hpair
          injection hpair with hp' hs'
          intro i hi
          subst hs'
          rfl
      | loop body =>
          by_cases hz : s.currentVal = 0
          · simp only [step, hz, if_true] at h
            injection h with hpair
            injection hpair with hp' hs'
            intro i hi
            subst hs'
            rfl
          · simp only [step, hz, if_false] at h
            injection h with hpair
            injection hpair with hp' hs'
            intro i hi
            subst hs'
            rfl

/--
A run whose configurations keep the pointer below `n` preserves every cell
above `n`: each step only modifies the current cell, which is below `n`.
-/
theorem RunsTo_preserves_tape_above {cfg : Program × State} (s_final : State) (n : Int)
    (h : RunsTo cfg s_final) (P : Program → State → Prop)
    (hPinit : P cfg.1 cfg.2)
    (hPstep : ∀ {p : Program} {s : State}, P p s → ∀ {p' : Program} {s' : State},
      step p s = some (p', s') → P p' s')
    (hPptr : ∀ {p : Program} {s : State}, P p s → s.ptr < n) :
    ∀ i : Int, n < i → s_final.tape i = cfg.2.tape i := by
  let Q : Program → State → Prop :=
    fun p s => P p s ∧ ∀ i : Int, n < i → s.tape i = cfg.2.tape i
  have hQfin : Q ([] : Program) s_final := by
    apply RunsTo_inv s_final Q h
    · constructor
      · exact hPinit
      · intro i hi
        rfl
    · intro p s hs p' s' hstep
      rcases hs with ⟨hP, hcells⟩
      constructor
      · exact hPstep hP hstep
      · intro i hi
        rw [step_preserves_tape_above n p s p' s' hstep (hPptr hP) i hi]
        exact hcells i hi
  rcases hQfin with ⟨hPfin, hcells⟩
  intro i hi
  exact hcells i hi

/-- Cells above the starting pointer are preserved by running `[+ -]`. -/
theorem runSeq_incVal_decVal_preserves (s : State) :
    ∀ i : Int, s.ptr + 1 < i → (runSeq [.inc_val, .dec_val] s).tape i = s.tape i := by
  let P_suffix : Program → State → Prop :=
    fun p s' => (p = [.inc_val, .dec_val] ∨ p = [.dec_val] ∨ p = []) ∧ s'.ptr = s.ptr
  have hruns : RunsTo ([.inc_val, .dec_val], s) (runSeq [.inc_val, .dec_val] s) := by
    apply RunsTo.step
    · rfl
    · apply RunsTo.step
      · rfl
      · exact RunsTo.halt _
  have hstep' : ∀ {p : Program} {s' : State}, P_suffix p s' → ∀ {p'' : Program} {s'' : State},
      step p s' = some (p'', s'') → P_suffix p'' s'' := by
    intro p s' hp p'' s'' hstep
    rcases hp with ⟨hp', hptr'⟩
    rcases hp' with hp1 | hp2 | hp3
    · subst p
      have hstep1 : step [.inc_val, .dec_val] s' = some ([.dec_val], s'.incVal) := by rfl
      rw [hstep1] at hstep
      injection hstep with hpair
      injection hpair with hp'' hs''
      subst p''
      subst s''
      constructor
      · exact Or.inr (Or.inl rfl)
      · rw [show s'.incVal.ptr = s'.ptr by rfl, hptr']
    · subst p
      have hstep2 : step [.dec_val] s' = some ([], s'.decVal) := by rfl
      rw [hstep2] at hstep
      injection hstep with hpair
      injection hpair with hp'' hs''
      subst p''
      subst s''
      constructor
      · exact Or.inr (Or.inr rfl)
      · rw [show s'.decVal.ptr = s'.ptr by rfl, hptr']
    · subst p
      simp only [step] at hstep
      cases hstep
  have hPptr : ∀ {p : Program} {s' : State}, P_suffix p s' → s'.ptr < s.ptr + 1 := by
    intro p s' hp
    rcases hp with ⟨hp', hptr'⟩
    rw [hptr']
    omega
  have hpres := RunsTo_preserves_tape_above (runSeq [.inc_val, .dec_val] s)
    (s.ptr + 1) hruns P_suffix (by
      constructor
      · exact Or.inl rfl
      · rfl)
    hstep' hPptr
  exact hpres

end LeanBF
