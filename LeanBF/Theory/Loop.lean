/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Compiler
import LeanBF.Core.Semantics
import Mathlib.Tactic.Ring

/-!
# Loop Correctness

Lemmas about `run` for loop-free instruction sequences and for the loops of
`Compiler.ifZeroElse`, whose bodies contain only pointer moves and cell
increments. These are the foundation for the dispatch simulation.

## Main definitions

* `stepOne`: The state effect of a single non-loop instruction.
* `LoopFree`: A program with no `[` instruction.
* `runSeq`: Sequentially execute a loop-free program.
* `copyLoop`: The `ifZeroElse` copy loop.

## Theorems

* `step_cons_stepOne`: A non-loop instruction steps to its `stepOne` effect.
* `loop_free_cons`: A non-loop head keeps a program loop-free.
* `loop_free_replicate`: Replicating a non-loop instruction is loop-free.
* `loop_free_append`: Concatenating loop-free programs is loop-free.
* `loop_free_single`: A single non-loop instruction is loop-free.
* `loop_free_movePtr`: `movePtr` produces loop-free code.
* `run_length_loop_free`: A loop-free program is fully executed in as many
  steps as it has instructions.
* `run_append`: Splitting a run across a loop-free prefix and its tail.
* `runSeq_append`: Sequential execution composes across concatenation.
* `runSeq_replicate_inc_ptr`: `n` pointer-right moves move the pointer `n`
  cells right.
* `runSeq_replicate_dec_ptr`: `n` pointer-left moves move the pointer `n`
  cells left.
* `runSeq_replicate_inc_ptr_tape`: Pointer moves do not change the tape.
* `runSeq_replicate_dec_ptr_tape`: Pointer moves do not change the tape.
* `runSeq_movePtr_ptr`: `movePtr` moves the pointer to its target.
* `runSeq_movePtr_tape`: `movePtr` does not change the tape.
* `runSeq_replicate_inc_ptr_io`: Pointer moves do not change the input or
  output.
* `runSeq_replicate_dec_ptr_io`: Pointer moves do not change the input or
  output.
* `runSeq_movePtr_io`: `movePtr` does not change the input or output.
* `loop_free_copyLoopBody`: The copy loop body is loop-free.

The ifZeroElse copy-loop effect lemma (the loop moves the tested value into
its three scratch cells) needs composed tape-cell reasoning and is the next
step.
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

/-- The copy loop: `[test - s1 + s2 + s4 +]`, moving the tested value into
    three cells. -/
def copyLoop (test s1 s2 s4 : Int) : Program :=
  [.loop (
    [.dec_val] ++
    Compiler.movePtr test s1 ++ [.inc_val] ++
    Compiler.movePtr s1 s2 ++ [.inc_val] ++
    Compiler.movePtr s2 s4 ++ [.inc_val] ++
    Compiler.movePtr s4 test
  )]

/-- The body of the copy loop: one iteration decrements `test` and
    increments `s1`, `s2`, and `s4`. -/
def copyLoopBody (test s1 s2 s4 : Int) : Program :=
  [.dec_val] ++
    (Compiler.movePtr test s1 ++
      ([.inc_val] ++
        (Compiler.movePtr s1 s2 ++
          ([.inc_val] ++
            (Compiler.movePtr s2 s4 ++
              ([.inc_val] ++ Compiler.movePtr s4 test))))))

/-- The state after one iteration of the copy loop. -/
def copyLoopStep (test s1 s2 s4 : Int) (a b c v : Nat) (s : State) : State :=
  { s with
    tape := fun i =>
      if i = test then v else
      if i = s1 then a + 1 else
      if i = s2 then b + 1 else
      if i = s4 then c + 1 else
      s.tape i }

/-- The state after the copy loop has run to completion. -/
def copyLoopPost (test s1 s2 s4 : Int) (a b c v : Nat) (s : State) : State :=
  { s with
    tape := fun i =>
      if i = test then 0 else
      if i = s1 then a + v else
      if i = s2 then b + v else
      if i = s4 then c + v else
      s.tape i }

/-- The copy loop body is loop-free. -/
theorem loop_free_copyLoopBody (test s1 s2 s4 : Int) :
    LoopFree (copyLoopBody test s1 s2 s4) := by
  unfold copyLoopBody
  apply loop_free_append
  · exact loop_free_single .dec_val (by intro body h'; cases h')
  · apply loop_free_append
    · exact loop_free_movePtr test s1
    · apply loop_free_append
      · exact loop_free_single .inc_val (by intro body h'; cases h')
      · apply loop_free_append
        · exact loop_free_movePtr s1 s2
        · apply loop_free_append
          · exact loop_free_single .inc_val (by intro body h'; cases h')
          · apply loop_free_append
            · exact loop_free_movePtr s2 s4
            · apply loop_free_append
              · exact loop_free_single .inc_val (by intro body h'; cases h')
              · exact loop_free_movePtr s4 test

end LeanBF
