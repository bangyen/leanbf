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
* `runSeq_copyLoopBody`: Running the copy loop body once produces copyLoopStep.
* `run_copyLoop`: The copy loop moves the tested value into three cells.
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

/-- The copy loop: `[test - s1 + s2 + s4 +]`, moving the tested value into
    three cells. -/
def copyLoop (test s1 s2 s4 : Int) : Program :=
  [.loop (copyLoopBody test s1 s2 s4)]

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

/-- The state reached after the first cell write of the copy loop body: the
    tested cell is decremented. -/
def copyLoopBodyDec (test : Int) (v : Nat) (s : State) : State :=
  { s with tape := fun i => if i = test then v else s.tape i }

/-- Running the copy loop body once produces `copyLoopStep`. -/
theorem runSeq_copyLoopBody (test s1 s2 s4 : Int) (a b c v : Nat) (s : State)
    (hptr : s.ptr = test) (hv : s.tape test = v + 1)
    (h1 : s.tape s1 = a) (h2 : s.tape s2 = b) (h4 : s.tape s4 = c)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s4 ∧ s1 ≠ s2 ∧ s1 ≠ s4 ∧ s2 ≠ s4) :
    runSeq (copyLoopBody test s1 s2 s4) s = copyLoopStep test s1 s2 s4 a b c v s := by
  let u1 : State := { s with tape := fun i => if i = test then v else s.tape i }
  have hu1 : runSeq [.dec_val] s = u1 := by
    apply State.ext
    · simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell, hptr]
    · funext i
      simp only [runSeq, stepOne, u1, State.decVal, State.modifyCell]
      by_cases hi : i = test
      · simp only [hi, hptr, hv, Nat.add_sub_cancel]
      · simp only [hptr, if_neg hi]
    · rfl
    · rfl
  have hu1ptr : u1.ptr = test := by simp only [u1, hptr]
  let u2 : State := { u1 with ptr := s1 }
  have hu2 : runSeq (Compiler.movePtr test s1) u1 = u2 := by
    apply State.ext
    · simp only [u2, runSeq_movePtr_ptr test s1 u1 hu1ptr]
    · simp only [u2, runSeq_movePtr_tape test s1 u1]
    · rw [(runSeq_movePtr_io test s1 u1).1]
    · rw [(runSeq_movePtr_io test s1 u1).2]
  have hu2ptr : u2.ptr = s1 := rfl
  have hu2tape_s1 : u2.tape s1 = a := by
    simp only [u2, u1]
    rw [if_neg (Ne.symm hsep.1)]
    exact h1
  let u3 : State := { u2 with tape := fun i => if i = s1 then a + 1 else u2.tape i }
  have hu3 : runSeq [.inc_val] u2 = u3 := by
    apply State.ext
    · simp only [runSeq, stepOne, u3, State.incVal, State.modifyCell, hu2ptr]
    · funext i
      simp only [runSeq, stepOne, u3, State.incVal, State.modifyCell]
      by_cases hi : i = s1
      · simp only [hi, hu2ptr, hu2tape_s1]
      · simp only [hu2ptr, if_neg hi]
    · rfl
    · rfl
  have hu3ptr : u3.ptr = s1 := rfl
  let u4 : State := { u3 with ptr := s2 }
  have hu4 : runSeq (Compiler.movePtr s1 s2) u3 = u4 := by
    apply State.ext
    · simp only [u4, runSeq_movePtr_ptr s1 s2 u3 hu3ptr]
    · simp only [u4, runSeq_movePtr_tape s1 s2 u3]
    · rw [(runSeq_movePtr_io s1 s2 u3).1]
    · rw [(runSeq_movePtr_io s1 s2 u3).2]
  have hu4ptr : u4.ptr = s2 := rfl
  have hu4tape_s2 : u4.tape s2 = b := by
    simp only [u4, u3, u2, u1]
    rw [if_neg (Ne.symm hsep.2.2.2.1), if_neg (Ne.symm hsep.2.1)]
    exact h2
  let u5 : State := { u4 with tape := fun i => if i = s2 then b + 1 else u4.tape i }
  have hu5 : runSeq [.inc_val] u4 = u5 := by
    apply State.ext
    · simp only [runSeq, stepOne, u5, State.incVal, State.modifyCell, hu4ptr]
    · funext i
      simp only [runSeq, stepOne, u5, State.incVal, State.modifyCell]
      by_cases hi : i = s2
      · simp only [hi, hu4ptr, hu4tape_s2]
      · simp only [hu4ptr, if_neg hi]
    · rfl
    · rfl
  have hu5ptr : u5.ptr = s2 := rfl
  let u6 : State := { u5 with ptr := s4 }
  have hu6 : runSeq (Compiler.movePtr s2 s4) u5 = u6 := by
    apply State.ext
    · simp only [u6, runSeq_movePtr_ptr s2 s4 u5 hu5ptr]
    · simp only [u6, runSeq_movePtr_tape s2 s4 u5]
    · rw [(runSeq_movePtr_io s2 s4 u5).1]
    · rw [(runSeq_movePtr_io s2 s4 u5).2]
  have hu6ptr : u6.ptr = s4 := rfl
  have hu6tape_s4 : u6.tape s4 = c := by
    simp only [u6, u5, u4, u3, u2, u1]
    rw [if_neg (Ne.symm hsep.2.2.2.2.2), if_neg (Ne.symm hsep.2.2.2.2.1),
      if_neg (Ne.symm hsep.2.2.1)]
    exact h4
  let u7 : State := { u6 with tape := fun i => if i = s4 then c + 1 else u6.tape i }
  have hu7 : runSeq [.inc_val] u6 = u7 := by
    apply State.ext
    · simp only [runSeq, stepOne, u7, State.incVal, State.modifyCell, hu6ptr]
    · funext i
      simp only [runSeq, stepOne, u7, State.incVal, State.modifyCell]
      by_cases hi : i = s4
      · simp only [hi, hu6ptr, hu6tape_s4]
      · simp only [hu6ptr, if_neg hi]
    · rfl
    · rfl
  have hu7ptr : u7.ptr = s4 := rfl
  let u8 : State := { u7 with ptr := test }
  have hu8 : runSeq (Compiler.movePtr s4 test) u7 = u8 := by
    apply State.ext
    · simp only [u8, runSeq_movePtr_ptr s4 test u7 hu7ptr]
    · simp only [u8, runSeq_movePtr_tape s4 test u7]
    · rw [(runSeq_movePtr_io s4 test u7).1]
    · rw [(runSeq_movePtr_io s4 test u7).2]
  -- peel the body and rewrite each segment
  change runSeq
    ([.dec_val] ++ (Compiler.movePtr test s1 ++
      ([.inc_val] ++ (Compiler.movePtr s1 s2 ++
        ([.inc_val] ++ (Compiler.movePtr s2 s4 ++
          ([.inc_val] ++ Compiler.movePtr s4 test))))))) s = copyLoopStep test s1 s2 s4 a b c v s
  rw [runSeq_append]
  rw [hu1]
  rw [runSeq_append]
  rw [hu2]
  rw [runSeq_append]
  rw [hu3]
  rw [runSeq_append]
  rw [hu4]
  rw [runSeq_append]
  rw [hu5]
  rw [runSeq_append]
  rw [hu6]
  rw [runSeq_append]
  rw [hu7]
  rw [hu8]
  -- u8 = copyLoopStep
  apply State.ext
  · simp only [u8, copyLoopStep, hptr]
  · funext i
    simp only [u8, u7, u6, u5, u4, u3, u2, u1, copyLoopStep]
    by_cases h1i : i = test
    · simp only [h1i, if_neg hsep.2.2.1, if_neg hsep.2.1, if_neg hsep.1, if_true]
    · by_cases h2i : i = s1
      · simp only [h2i, if_neg hsep.2.2.2.2.1, if_neg hsep.2.2.2.1,
          if_neg (Ne.symm hsep.1), if_true]
      · by_cases h3i : i = s2
        · simp only [h3i, if_neg hsep.2.2.2.2.2, if_neg (Ne.symm hsep.2.2.2.1),
            if_neg (Ne.symm hsep.2.1), if_true]
        · by_cases h4i : i = s4
          · simp only [h4i, if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
              if_neg (Ne.symm hsep.2.2.2.2.2), if_true]
          · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
  · rfl
  · rfl

/-- The copy loop moves the tested value into three cells: from a state with
    `test` holding `v` and `s1`/`s2`/`s4` holding `a`/`b`/`c`, it reaches a
    state with `test` holding `0` and `s1`/`s2`/`s4` holding `a+v`/`b+v`/`c+v`,
    leaving the pointer and every other cell unchanged. -/
theorem run_copyLoop (v : Nat) (test s1 s2 s4 : Int) (a b c : Nat) (s : State)
    (hptr : s.ptr = test) (hv : s.tape test = v) (h1 : s.tape s1 = a)
    (h2 : s.tape s2 = b) (h4 : s.tape s4 = c)
    (hsep : test ≠ s1 ∧ test ≠ s2 ∧ test ≠ s4 ∧ s1 ≠ s2 ∧ s1 ≠ s4 ∧ s2 ≠ s4) :
    ∃ n : Nat, run n (copyLoop test s1 s2 s4) s = some (copyLoopPost test s1 s2 s4 a b c v s) := by
  induction v generalizing a b c s with
  | zero =>
      refine ⟨1, ?_⟩
      have hzero : s.currentVal = 0 := by
        simp only [State.currentVal, hptr, hv]
      have hstep : step (copyLoop test s1 s2 s4) s = some ([], s) := by
        simp only [copyLoop, step, if_pos hzero]
      simp only [run, hstep]
      congr 1
      apply State.ext
      · rfl
      · funext i
        simp only [copyLoopPost]
        by_cases h1i : i = test
        · simp only [h1i, if_true, hv]
        · by_cases h2i : i = s1
          · simp only [h2i, if_neg (Ne.symm hsep.1), if_true, h1, Nat.add_zero]
          · by_cases h3i : i = s2
            · simp only [h3i, if_neg (Ne.symm hsep.2.1), if_neg (Ne.symm hsep.2.2.2.1),
                if_true, h2, Nat.add_zero]
            · by_cases h4i : i = s4
              · simp only [h4i, if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
                  if_neg (Ne.symm hsep.2.2.2.2.2), if_true, h4, Nat.add_zero]
              · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
      · rfl
      · rfl
  | succ v ih =>
      let s' := copyLoopStep test s1 s2 s4 a b c v s
      have hs'ptr : s'.ptr = test := by simp only [s', copyLoopStep, hptr]
      have hs'test : s'.tape test = v := by
        simp only [s', copyLoopStep]
        rfl
      have hs's1 : s'.tape s1 = a + 1 := by
        simp only [s', copyLoopStep]
        rw [if_neg (Ne.symm hsep.1), if_true]
      have hs's2 : s'.tape s2 = b + 1 := by
        simp only [s', copyLoopStep]
        rw [if_neg (Ne.symm hsep.2.1), if_neg (Ne.symm hsep.2.2.2.1), if_true]
      have hs's4 : s'.tape s4 = c + 1 := by
        simp only [s', copyLoopStep]
        rw [if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
          if_neg (Ne.symm hsep.2.2.2.2.2), if_true]
      have hne : s.currentVal ≠ 0 := by
        simp only [State.currentVal, hptr, hv]
        exact Nat.succ_ne_zero v
      have hrunSeq : runSeq (copyLoopBody test s1 s2 s4) s = s' := by
        simpa only [s'] using
          (runSeq_copyLoopBody test s1 s2 s4 a b c v s hptr hv h1 h2 h4 hsep)
      rcases ih (a + 1) (b + 1) (c + 1) s' hs'ptr hs'test hs's1 hs's2 hs's4 with ⟨n, hn⟩
      refine ⟨1 + (copyLoopBody test s1 s2 s4).length + n, ?_⟩
      rw [show 1 + (copyLoopBody test s1 s2 s4).length + n =
        Nat.succ ((copyLoopBody test s1 s2 s4).length + n) by
        rw [Nat.succ_eq_add_one]
        ring]
      change run (Nat.succ ((copyLoopBody test s1 s2 s4).length + n))
        [.loop (copyLoopBody test s1 s2 s4)] s = some (copyLoopPost test s1 s2 s4 a b c (v + 1) s)
      simp only [run, step, if_neg hne]
      rw [List.append_nil]
      rw [run_append]
      · rw [hrunSeq]
        change run n (copyLoop test s1 s2 s4) s' = some (copyLoopPost test s1 s2 s4 a b c (v + 1) s)
        rw [hn]
        congr 1
        apply State.ext
        · rfl
        · funext i
          simp only [copyLoopPost, copyLoopStep, s']
          by_cases h1i : i = test
          · simp only [h1i, if_true]
          · by_cases h2i : i = s1
            · simp only [h2i, if_neg (Ne.symm hsep.1), if_true]
              ring
            · by_cases h3i : i = s2
              · simp only [h3i, if_neg (Ne.symm hsep.2.1), if_neg (Ne.symm hsep.2.2.2.1), if_true]
                ring
              · by_cases h4i : i = s4
                · simp only [h4i, if_neg (Ne.symm hsep.2.2.1), if_neg (Ne.symm hsep.2.2.2.2.1),
                    if_neg (Ne.symm hsep.2.2.2.2.2), if_true]
                  ring
                · simp only [if_neg h1i, if_neg h2i, if_neg h3i, if_neg h4i]
        · rfl
        · rfl
      · exact loop_free_copyLoopBody test s1 s2 s4

end LeanBF
