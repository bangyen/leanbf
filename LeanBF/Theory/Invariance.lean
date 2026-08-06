/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics
import LeanBF.Core.State
import LeanBF.Theory.BodyLoop
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
  so every cell at or above the pointer's bound is preserved.
* `RunsTo_preserves_tape_above`: A run whose configurations keep the pointer
  below n preserves every cell at or above n.
* `runSeq_incVal_decVal_preserves`: Cells at or above the starting pointer
  are preserved by `[+ -]` run sequentially.
* `drop_replicate_succ`: Dropping `k` from `k + 1` copies of `a` yields `a`
  followed by dropping `k + 1`.
* `movePtr_incVal_preserves_above`: Running the compiler's window sweep
  (`movePtr 0 16 ++ [+ ]`) preserves every cell above the window.
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

/-- A single step only modifies the current cell, so every cell at or above
    the pointer's bound is preserved. -/
theorem step_preserves_tape_above (n : Int) (p : Program) (s : State) (p' : Program) (s' : State)
    (h : step p s = some (p', s')) (hptr : s.ptr < n) :
    ∀ i : Int, n ≤ i → s'.tape i = s.tape i := by
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
A run whose configurations keep the pointer below `n` preserves every cell at
or above `n`: each step only modifies the current cell, which is below `n`.
-/
theorem RunsTo_preserves_tape_above {cfg : Program × State} (s_final : State) (n : Int)
    (h : RunsTo cfg s_final) (P : Program → State → Prop)
    (hPinit : P cfg.1 cfg.2)
    (hPstep : ∀ {p : Program} {s : State}, P p s → ∀ {p' : Program} {s' : State},
      step p s = some (p', s') → P p' s')
    (hPptr : ∀ {p : Program} {s : State}, P p s → s.ptr < n) :
    ∀ i : Int, n ≤ i → s_final.tape i = cfg.2.tape i := by
  let Q : Program → State → Prop :=
    fun p s => P p s ∧ ∀ i : Int, n ≤ i → s.tape i = cfg.2.tape i
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
  intro i hi
  exact hpres i (by omega)

lemma drop_replicate_succ {α : Type} (n k : Nat) (a : α) (hk : k < n) :
    List.drop k (List.replicate n a) = a :: List.drop (k + 1) (List.replicate n a) := by
  induction k generalizing n with
  | zero =>
      cases n with
      | zero => cases hk
      | succ n => rfl
  | succ k ih =>
      cases n with
      | zero => cases hk
      | succ n =>
          have hk' : k < n := by omega
          rw [List.replicate_succ]
          rw [List.drop_succ_cons]
          rw [List.drop_succ_cons]
          rw [ih n hk']

/-- Running `movePtr 0 16 ++ [+ ]` across the window cells preserves every
    cell above the window. -/
theorem movePtr_incVal_preserves_above (s : State) (hptr : s.ptr = 0) :
    ∀ i : Int, 16 < i → (runSeq (Compiler.movePtr 0 16 ++ [.inc_val]) s).tape i = s.tape i := by
  let prog : Program := Compiler.movePtr 0 16 ++ [.inc_val]
  let cfg : Program × State := (prog, s)
  have hloopfree : LoopFree prog := by
    unfold prog
    exact loop_free_append (Compiler.movePtr 0 16) [.inc_val] (loop_free_movePtr 0 16)
      (loop_free_single .inc_val (by intro body h; cases h))
  have hruns : RunsTo cfg (runSeq prog s) := runsTo_of_loopFree prog s hloopfree
  let P : Program → State → Prop := fun p s' =>
    (∃ k : Nat, k ≤ 16 ∧ p = List.drop k (Compiler.movePtr 0 16) ++ [.inc_val] ∧ s'.ptr = k) ∨
    (p = [] ∧ s'.ptr = 16)
  have hPinit : P cfg.1 cfg.2 := by
    exact Or.inl ⟨0, by omega, by simp only [cfg, prog, List.drop], by rw [hptr]; rfl⟩
  have hPstep : ∀ {p : Program} {s' : State}, P p s' → ∀ {p'' : Program} {s'' : State},
      step p s' = some (p'', s'') → P p'' s'' := by
    intro p s' hp p'' s'' hstep
    rcases hp with hpre | hfinal
    · rcases hpre with ⟨k, hk, hp, hptrk⟩
      by_cases hk16 : k < 16
      · have hcons : List.drop k (Compiler.movePtr 0 16) =
            .inc_ptr :: List.drop (k + 1) (Compiler.movePtr 0 16) := by
          change List.drop k (List.replicate 16 (.inc_ptr : Instruction)) =
            (.inc_ptr : Instruction) ::
              List.drop (k + 1) (List.replicate 16 (.inc_ptr : Instruction))
          exact drop_replicate_succ 16 k (.inc_ptr : Instruction) hk16
        have hstep' : step (List.drop k (Compiler.movePtr 0 16) ++ [.inc_val]) s' =
            some (List.drop (k + 1) (Compiler.movePtr 0 16) ++ [.inc_val], s'.incPtr) := by
          rw [hcons]
          rfl
        rw [hp, hstep'] at hstep
        injection hstep with hpair
        injection hpair with hp'' hs''
        subst p''
        subst s''
        exact Or.inl ⟨k + 1, by omega, rfl, by
          change s'.ptr + 1 = (k + 1 : Int)
          rw [hptrk]⟩
      · have hk16' : k = 16 := by omega
        subst k
        have hdrop16 : List.drop 16 (Compiler.movePtr 0 16) = [] := by
          change List.drop 16 (List.replicate 16 (.inc_ptr : Instruction)) = []
          rfl
        have hstep' : step [.inc_val] s' = some ([], s'.incVal) := by rfl
        rw [hp, hdrop16] at hstep
        change step [.inc_val] s' = some (p'', s'') at hstep
        rw [hstep'] at hstep
        injection hstep with hpair
        injection hpair with hp'' hs''
        subst p''
        subst s''
        exact Or.inr ⟨rfl, by
          change s'.ptr = (16 : Int)
          rw [hptrk]
          norm_num⟩
    · rcases hfinal with ⟨hp, hptr'⟩
      subst p
      simp only [step] at hstep
      cases hstep
  have hPptr : ∀ {p : Program} {s' : State}, P p s' → s'.ptr < 17 := by
    intro p s' hp
    rcases hp with hpre | hfinal
    · rcases hpre with ⟨k, hk, hp, hptrk⟩
      rw [hptrk]
      omega
    · rcases hfinal with ⟨hp, hptr'⟩
      rw [hptr']
      omega
  have hpres := RunsTo_preserves_tape_above (runSeq prog s) (17 : Int) hruns P hPinit hPstep hPptr
  intro i hi
  exact hpres i (by omega)

end LeanBF
