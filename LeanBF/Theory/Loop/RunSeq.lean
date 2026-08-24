/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Compiler
import LeanBF.Core.Semantics
import LeanBF.Theory.Loop.Basics
import Mathlib.Tactic.Ring

/-!
# Run Facts

Run-level facts: a loop-free program runs to `runSeq` completion, runs split
across a loop-free prefix and its tail, and repeated pointer moves behave as
expected.

## Theorems

* `run_length_loop_free`: A loop-free program runs to `runSeq` completion.
* `stepsToHalt_loop_free`: A loop-free program halts in exactly as many
  steps as it has instructions.
* `halts_of_loopFree`: A loop-free program always halts.
* `run_append`: Splitting a run across a loop-free prefix and its tail.
* `runSeq_append`: Sequential execution distributes across concatenation.
* `runSeq_replicate_inc_ptr`: Repeating `>` moves the pointer.
* `runSeq_replicate_dec_ptr`: Repeating `<` moves the pointer.
* `runSeq_replicate_inc_ptr_tape`: Repeated `>` leaves the tape unchanged.
* `runSeq_replicate_dec_ptr_tape`: Repeated `<` leaves the tape unchanged.
* `runSeq_movePtr_ptr`: `movePtr` ends with the pointer on its target.
* `runSeq_movePtr_tape`: `movePtr` leaves the tape unchanged.
* `runSeq_replicate_inc_ptr_io`: Repeated `>` leaves the I/O unchanged.
* `runSeq_replicate_dec_ptr_io`: Repeated `<` leaves the I/O unchanged.
* `runSeq_movePtr_io`: `movePtr` leaves the I/O unchanged.
-/

namespace LeanBF

/-- A loop-free program is fully executed in as many steps as it has
    instructions. -/
theorem run_length_loop_free : ∀ (A : Program) (s : State),
    LoopFree A → run A.length A s = some (runSeq A s) := by
  intro A
  induction A with
  | nil => intro s h; rfl
  | cons i rest ih =>
      intro s h
      rw [show (i :: rest).length = rest.length + 1 by rfl]
      simp only [run]
      rw [step_cons_stepOne i rest s h.1]
      change run rest.length rest (stepOne i s) = some (runSeq (i :: rest) s)
      rw [ih (stepOne i s) h.2]
      rfl

/-- Splitting a run across a loop-free prefix and its tail. -/
theorem run_append : ∀ (n : Nat) (A B : Program) (s : State),
    LoopFree A → run (A.length + n) (A ++ B) s = run n B (runSeq A s) := by
  intro n A
  induction A with
  | nil =>
      intro B s h
      rw [show ([] : Program).length = 0 by rfl]
      rw [show ([] : Program) ++ B = B by rfl]
      rw [show runSeq ([] : Program) s = s by rfl]
      rw [Nat.zero_add]
  | cons i rest ih =>
      intro B s h
      rw [show (i :: rest).length + n = rest.length + 1 + n by rfl]
      rw [show rest.length + 1 + n = Nat.succ (rest.length + n) by
        rw [Nat.succ_eq_add_one]
        ring]
      change run (Nat.succ (rest.length + n)) (i :: (rest ++ B)) s = run n B (runSeq (i :: rest) s)
      simp only [run]
      rw [step_cons_stepOne i (rest ++ B) s h.1]
      change run (rest.length + n) (rest ++ B) (stepOne i s) = run n B (runSeq (i :: rest) s)
      rw [ih B (stepOne i s) h.2]
      rfl

/-- Sequential execution composes across concatenation. -/
theorem runSeq_append (A B : Program) : ∀ (s : State),
    runSeq (A ++ B) s = runSeq B (runSeq A s) := by
  induction A with
  | nil => intro s; rfl
  | cons i rest ih =>
      intro s
      change runSeq (i :: (rest ++ B)) s = runSeq B (runSeq (i :: rest) s)
      simp only [runSeq]
      rw [ih (stepOne i s)]

/-- A run over `n` pointer-right moves moves the pointer `n` cells right. -/
theorem runSeq_replicate_inc_ptr (n : Nat) : ∀ (s : State),
    (runSeq (List.replicate n .inc_ptr) s).ptr = s.ptr + (n : Int) := by
  induction n with
  | zero => intro s; simp only [List.replicate, runSeq]; norm_num
  | succ n ih =>
      intro s
      rw [List.replicate_succ]
      simp only [runSeq, stepOne]
      rw [ih (s.incPtr)]
      simp only [State.incPtr]
      norm_num
      ring

/-- A run over `n` pointer-left moves moves the pointer `n` cells left. -/
theorem runSeq_replicate_dec_ptr (n : Nat) : ∀ (s : State),
    (runSeq (List.replicate n .dec_ptr) s).ptr = s.ptr - (n : Int) := by
  induction n with
  | zero => intro s; simp only [List.replicate, runSeq]; norm_num
  | succ n ih =>
      intro s
      rw [List.replicate_succ]
      simp only [runSeq, stepOne]
      rw [ih (s.decPtr)]
      simp only [State.decPtr]
      norm_num
      ring

/-- Pointer moves do not change the tape. -/
theorem runSeq_replicate_inc_ptr_tape (n : Nat) : ∀ (s : State),
    (runSeq (List.replicate n .inc_ptr) s).tape = s.tape := by
  induction n with
  | zero => intro s; simp only [List.replicate, runSeq]
  | succ n ih =>
      intro s
      rw [List.replicate_succ]
      simp only [runSeq, stepOne]
      rw [ih (s.incPtr)]
      simp only [State.incPtr]

/-- Pointer moves do not change the tape. -/
theorem runSeq_replicate_dec_ptr_tape (n : Nat) : ∀ (s : State),
    (runSeq (List.replicate n .dec_ptr) s).tape = s.tape := by
  induction n with
  | zero => intro s; simp only [List.replicate, runSeq]
  | succ n ih =>
      intro s
      rw [List.replicate_succ]
      simp only [runSeq, stepOne]
      rw [ih (s.decPtr)]
      simp only [State.decPtr]

/-- `movePtr` moves the pointer to its target. -/
theorem runSeq_movePtr_ptr (i j : Int) (s : State) (hptr : s.ptr = i) :
    (runSeq (Compiler.movePtr i j) s).ptr = j := by
  unfold Compiler.movePtr
  by_cases h : i < j
  · rw [if_pos h]
    rw [runSeq_replicate_inc_ptr (j - i).toNat s]
    rw [hptr]
    have hnn : 0 ≤ j - i := sub_nonneg.mpr (Int.le_of_lt h)
    rw [Int.toNat_of_nonneg hnn]
    ring
  · rw [if_neg h]
    rw [runSeq_replicate_dec_ptr (i - j).toNat s]
    rw [hptr]
    have hnn : 0 ≤ i - j := sub_nonneg.mpr (Int.le_of_not_gt h)
    rw [Int.toNat_of_nonneg hnn]
    ring

/-- `movePtr` does not change the tape. -/
theorem runSeq_movePtr_tape (i j : Int) (s : State) :
    (runSeq (Compiler.movePtr i j) s).tape = s.tape := by
  unfold Compiler.movePtr
  by_cases h : i < j
  · rw [if_pos h]
    exact runSeq_replicate_inc_ptr_tape (j - i).toNat s
  · rw [if_neg h]
    exact runSeq_replicate_dec_ptr_tape (i - j).toNat s

/-- Pointer moves do not change the input or output. -/
theorem runSeq_replicate_inc_ptr_io (n : Nat) : ∀ (s : State),
    (runSeq (List.replicate n .inc_ptr) s).input = s.input ∧
    (runSeq (List.replicate n .inc_ptr) s).output = s.output := by
  induction n with
  | zero => intro s; simp only [List.replicate, runSeq]; constructor <;> trivial
  | succ n ih =>
      intro s
      rw [List.replicate_succ]
      simp only [runSeq, stepOne]
      rw [(ih (s.incPtr)).1, (ih (s.incPtr)).2]
      simp only [State.incPtr]
      constructor <;> trivial

/-- Pointer moves do not change the input or output. -/
theorem runSeq_replicate_dec_ptr_io (n : Nat) : ∀ (s : State),
    (runSeq (List.replicate n .dec_ptr) s).input = s.input ∧
    (runSeq (List.replicate n .dec_ptr) s).output = s.output := by
  induction n with
  | zero => intro s; simp only [List.replicate, runSeq]; constructor <;> trivial
  | succ n ih =>
      intro s
      rw [List.replicate_succ]
      simp only [runSeq, stepOne]
      rw [(ih (s.decPtr)).1, (ih (s.decPtr)).2]
      simp only [State.decPtr]
      constructor <;> trivial

/-- `movePtr` does not change the input or output. -/
theorem runSeq_movePtr_io (i j : Int) (s : State) :
    (runSeq (Compiler.movePtr i j) s).input = s.input ∧
    (runSeq (Compiler.movePtr i j) s).output = s.output := by
  unfold Compiler.movePtr
  by_cases h : i < j
  · rw [if_pos h]
    exact runSeq_replicate_inc_ptr_io (j - i).toNat s
  · rw [if_neg h]
    exact runSeq_replicate_dec_ptr_io (i - j).toNat s

/-- A loop-free program takes exactly as many steps to halt as it has
    instructions, given at least that much fuel. -/
theorem stepsToHalt_loop_free : ∀ (A : Program) (s : State) (n : Nat),
    LoopFree A → A.length ≤ n → stepsToHalt n A s = A.length := by
  intro A
  induction A with
  | nil => intro s n h hn; cases n <;> rfl
  | cons i rest ih =>
      intro s n h hn
      cases n with
      | zero => simp only [List.length_cons] at hn; omega
      | succ k =>
          simp only [stepsToHalt, step_cons_stepOne i rest s h.1]
          rw [ih (stepOne i s) k h.2 (by simp only [List.length_cons] at hn; omega)]
          simp only [List.length_cons]

/-- A loop-free program always halts. -/
theorem halts_of_loopFree (A : Program) (s : State) (h : LoopFree A) : halts A s :=
  ⟨A.length + 1, by
    unfold haltsWithin
    rw [stepsToHalt_loop_free A s (A.length + 1) h (by omega)]
    omega⟩

end LeanBF
