/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Core.Compiler
import LeanBF.Core.Semantics
import Mathlib.Tactic.Ring

/-!
# Step and Run Basics

The `stepOne`/`runSeq` execution primitives, the `LoopFree` predicate, and
the single-step and loop-free lemmas.

## Main definitions

* `stepOne`: The effect of a single non-loop instruction.
* `LoopFree`: A program with no `[` instruction.
* `runSeq`: Sequentially execute a loop-free program.

## Theorems

* `step_cons_stepOne`: A non-loop instruction steps to its `stepOne` effect.
* `step_append`: Appending `B` to a program does not change the effect of its
  next step.
* `loop_free_cons`: Appending a loop-free instruction keeps a program
  loop-free.
* `loop_free_replicate`: Repeating an instruction `n` times keeps it
  loop-free.
* `loop_free_append`: Appending loop-free programs keeps them loop-free.
* `loop_free_single`: A single non-loop instruction is loop-free.
* `loop_free_movePtr`: `movePtr` produces loop-free code.
-/

namespace LeanBF

/-- The state effect of a single non-loop instruction. -/
def stepOne (i : Instruction) (s : State) : State :=
  match i with
  | .inc_ptr => s.incPtr
  | .dec_ptr => s.decPtr
  | .inc_val => s.incVal
  | .dec_val => s.decVal
  | .read =>
      match s.input with
      | [] => { s with tape := fun i => if i = s.ptr then 0 else s.tape i }
      | x :: xs => { s with tape := fun i => if i = s.ptr then x else s.tape i, input := xs }
  | .write => { s with output := s.currentVal :: s.output }
  | .loop _ => s

/-- A program with no `[` instruction. -/
def LoopFree : Program → Prop
  | [] => True
  | i :: rest => (∀ body : Program, i ≠ .loop body) ∧ LoopFree rest

/-- Sequentially execute a loop-free program. -/
def runSeq (prog : Program) (s : State) : State :=
  match prog with
  | [] => s
  | i :: rest => runSeq rest (stepOne i s)

/-- A non-loop instruction steps to its `stepOne` effect. -/
theorem step_cons_stepOne (i : Instruction) (rest : Program) (s : State)
    (h : ∀ body : Program, i ≠ .loop body) :
    step (i :: rest) s = some (rest, stepOne i s) := by
  cases i with
  | inc_ptr => rfl
  | dec_ptr => rfl
  | inc_val => rfl
  | dec_val => rfl
  | loop body => exact False.elim (h body rfl)
  | read =>
      cases h_in : s.input with
      | nil => simp only [step, stepOne, h_in]
      | cons x xs => simp only [step, stepOne, h_in]
  | write => rfl

/-- Appending `B` to a program does not change the effect of its next step. -/
theorem step_append (p B : Program) (s s1 : State) (p' : Program)
    (h : step p s = some (p', s1)) : step (p ++ B) s = some (p' ++ B, s1) := by
  cases p with
  | nil => simp only [step] at h; cases h
  | cons i rest =>
      cases i with
      | inc_ptr =>
          rw [step_cons_stepOne .inc_ptr rest s (by intro body h'; cases h')] at h
          change step (.inc_ptr :: (rest ++ B)) s = some (p' ++ B, s1)
          rw [step_cons_stepOne .inc_ptr (rest ++ B) s (by intro body h'; cases h')]
          injection h with hpair
          injection hpair with hrest hs1
          subst p'
          subst s1
          rfl
      | dec_ptr =>
          rw [step_cons_stepOne .dec_ptr rest s (by intro body h'; cases h')] at h
          change step (.dec_ptr :: (rest ++ B)) s = some (p' ++ B, s1)
          rw [step_cons_stepOne .dec_ptr (rest ++ B) s (by intro body h'; cases h')]
          injection h with hpair
          injection hpair with hrest hs1
          subst p'
          subst s1
          rfl
      | inc_val =>
          rw [step_cons_stepOne .inc_val rest s (by intro body h'; cases h')] at h
          change step (.inc_val :: (rest ++ B)) s = some (p' ++ B, s1)
          rw [step_cons_stepOne .inc_val (rest ++ B) s (by intro body h'; cases h')]
          injection h with hpair
          injection hpair with hrest hs1
          subst p'
          subst s1
          rfl
      | dec_val =>
          rw [step_cons_stepOne .dec_val rest s (by intro body h'; cases h')] at h
          change step (.dec_val :: (rest ++ B)) s = some (p' ++ B, s1)
          rw [step_cons_stepOne .dec_val (rest ++ B) s (by intro body h'; cases h')]
          injection h with hpair
          injection hpair with hrest hs1
          subst p'
          subst s1
          rfl
      | write =>
          rw [step_cons_stepOne .write rest s (by intro body h'; cases h')] at h
          change step (.write :: (rest ++ B)) s = some (p' ++ B, s1)
          rw [step_cons_stepOne .write (rest ++ B) s (by intro body h'; cases h')]
          injection h with hpair
          injection hpair with hrest hs1
          subst p'
          subst s1
          rfl
      | read =>
          cases h_in : s.input with
          | nil =>
              rw [step_cons_stepOne .read rest s (by intro body h'; cases h')] at h
              change step (.read :: (rest ++ B)) s = some (p' ++ B, s1)
              rw [step_cons_stepOne .read (rest ++ B) s (by intro body h'; cases h')]
              injection h with hpair
              injection hpair with hrest hs1
              subst p'
              subst s1
              rfl
          | cons x xs =>
              rw [step_cons_stepOne .read rest s (by intro body h'; cases h')] at h
              change step (.read :: (rest ++ B)) s = some (p' ++ B, s1)
              rw [step_cons_stepOne .read (rest ++ B) s (by intro body h'; cases h')]
              injection h with hpair
              injection hpair with hrest hs1
              subst p'
              subst s1
              rfl
      | loop body =>
          by_cases c : s.currentVal = 0
          · rw [step, if_pos c] at h
            change step ((.loop body) :: (rest ++ B)) s = some (p' ++ B, s1)
            rw [step, if_pos c]
            injection h with hpair
            injection hpair with hrest hs1
            subst p'
            subst s1
            rfl
          · rw [step, if_neg c] at h
            change step ((.loop body) :: (rest ++ B)) s = some (p' ++ B, s1)
            rw [step, if_neg c]
            injection h with hpair
            injection hpair with hrest hs1
            subst p'
            subst s1
            ac_rfl

/-- A non-loop head keeps a program loop-free. -/
theorem loop_free_cons (i : Instruction) (rest : Program) :
    (∀ body : Program, i ≠ .loop body) → LoopFree rest → LoopFree (i :: rest) := by
  intro hi hrest
  exact And.intro hi hrest

/-- Replicating a non-loop instruction is loop-free. -/
theorem loop_free_replicate (n : Nat) (i : Instruction) :
    (∀ body : Program, i ≠ .loop body) → LoopFree (List.replicate n i) := by
  intro hi
  induction n with
  | zero => simp only [List.replicate, LoopFree]
  | succ n ih => exact loop_free_cons i (List.replicate n i) hi ih

/-- Concatenating loop-free programs is loop-free. -/
theorem loop_free_append (A B : Program) :
    LoopFree A → LoopFree B → LoopFree (A ++ B) := by
  induction A with
  | nil => intro hA hB; simpa only [LoopFree] using hB
  | cons i rest ih =>
      intro hA hB
      rcases hA with ⟨hi, hrest⟩
      exact loop_free_cons i (rest ++ B) hi (ih hrest hB)

/-- A single non-loop instruction is loop-free. -/
theorem loop_free_single (i : Instruction) :
    (∀ body : Program, i ≠ .loop body) → LoopFree [i] := by
  intro hi
  change (∀ body : Program, i ≠ .loop body) ∧ LoopFree []
  exact And.intro hi (by simp only [LoopFree])

/-- `movePtr` produces loop-free code. -/
theorem loop_free_movePtr (i j : Int) : LoopFree (Compiler.movePtr i j) := by
  unfold Compiler.movePtr
  by_cases h : i < j
  · rw [if_pos h]
    exact loop_free_replicate _ .inc_ptr (by intro body h'; cases h')
  · rw [if_neg h]
    exact loop_free_replicate _ .dec_ptr (by intro body h'; cases h')

end LeanBF
