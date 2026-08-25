/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.BodyLoop
import LeanBF.Theory.Determinism
import LeanBF.Theory.Simulation

/-!
# Program Equivalence

Observational equivalence of programs: `A` and `B` are equivalent when they
reach exactly the same final states from every starting state. Because `step`
is a function, the reachable final state is unique
(`runsTo_deterministic`), so this says the two programs halt on the same
inputs and compute the same result when they do.

The tape lemmas in `Theory.State` pin down the effect of single cell
operations; this module gives the vocabulary to state the corresponding facts
about whole programs, and proves the first instances — the pointer moves
cancel, and so does `+ -`.

Equivalence is a congruence for `++` in each argument, proven from
`runsTo_append_factor`: every run of `A ++ C` factors through a state at
which `A` has halted. It is also a congruence for `loop`
(`progEquiv_loop`), by strong induction on the length of the halting run —
each iteration costs at least the loop-entry step, so the measure strictly
decreases. Together these let a rewrite be applied at any depth of
nesting.

## Main definitions

* `ProgEquiv`: Two programs reach the same final states from every state.

## Theorems

* `runsTo_of_step`: A run continues from the successor of its first step.
* `runsTo_nil_eq`: The empty program's runs end where they start.
* `runsTo_append_factor`: A run of an append factors through a halting state
  of its prefix.
* `progEquiv_refl`: `ProgEquiv` is reflexive.
* `progEquiv_symm`: `ProgEquiv` is symmetric.
* `progEquiv_trans`: `ProgEquiv` is transitive.
* `progEquiv_append_left`: Replacing a prefix by an equivalent program.
* `progEquiv_append_right`: Replacing a suffix by an equivalent program.
* `incVal_decVal_id`: `+ -` restores the state.
* `progEquiv_incPtr_decPtr`: `> <` is a no-op.
* `progEquiv_decPtr_incPtr`: `< >` is a no-op.
* `progEquiv_incVal_decVal`: `+ -` is a no-op.
* `decVal_incVal_ne_id`: `- +` is *not* a no-op, because cell values are
  natural numbers and decrement truncates at zero.
* `runsTo_of_runsExactly`: An exact run witnesses a `RunsTo` chain.
* `runsTo_loop_of_progEquiv`: One direction of `progEquiv_loop`.
* `progEquiv_loop`: Equivalent loop bodies give equivalent loops.
-/

namespace LeanBF

/-- A run continues from the successor of its first step. -/
theorem runsTo_of_step {P : Program} {s s2 : State} {P' : Program} {t : State}
    (hstep : step P s = some (P', s2)) (h : RunsTo (P, s) t) : RunsTo (P', s2) t := by
  cases h with
  | halt s0 =>
      rw [step_empty] at hstep
      exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  | step _ _ s3 p3 _ hstep3 hrest3 =>
      have heq : (P', s2) = (p3, s3) := step_deterministic P s _ _ hstep hstep3
      rw [heq]
      exact hrest3

/-- The empty program halts immediately, so its runs end where they start. -/
theorem runsTo_nil_eq {s t : State} (h : RunsTo (([] : Program), s) t) : t = s := by
  cases h with
  | halt => rfl
  | step _ _ _ _ _ hstep _ =>
      rw [step_empty] at hstep
      exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-- Every run of `A ++ C` factors through a state at which `A` has halted.
    This is the converse of `RunsTo_append`, and is what makes `ProgEquiv` a
    congruence for `++`. -/
theorem runsTo_append_factor (cfg : Program × State) (t : State) (h : RunsTo cfg t) :
    ∀ (A C : Program) (s : State), cfg = (A ++ C, s) →
      ∃ s', RunsTo (A, s) s' ∧ RunsTo (C, s') t := by
  induction h with
  | halt s0 =>
      intro A C s heq
      have hfst : A ++ C = [] := (congrArg Prod.fst heq).symm
      have hA : A = [] ∧ C = [] := by
        simpa only [List.append_eq_nil_iff] using hfst
      have hs : s = s0 := (congrArg Prod.snd heq).symm
      subst hs
      rw [hA.1, hA.2]
      exact ⟨s, RunsTo.halt s, RunsTo.halt s⟩
  | step p s0 s2 p' s_fin hstep hrest ih =>
      intro A C s heq
      have hp : p = A ++ C := congrArg Prod.fst heq
      have hs : s0 = s := congrArg Prod.snd heq
      subst hp
      subst hs
      cases A with
      | nil =>
          exact ⟨s0, RunsTo.halt s0, by
            simpa only [List.nil_append] using RunsTo.step _ s0 s2 p' s_fin hstep hrest⟩
      | cons i rest =>
          rcases hstepA : step (i :: rest) s0 with _ | ⟨q, s3⟩
          · exact absurd hstepA (step_cons_ne_none i rest s0)
          · have happ : step ((i :: rest) ++ C) s0 = some (q ++ C, s3) :=
              step_append (i :: rest) C s0 s3 q hstepA
            have heq2 : (p', s2) = (q ++ C, s3) :=
              step_deterministic ((i :: rest) ++ C) s0 _ _ hstep happ
            rw [heq2] at hrest
            rcases ih q C s3 heq2 with ⟨s', hq, hC⟩
            exact ⟨s', RunsTo.step (i :: rest) s0 s3 q s' hstepA hq, hC⟩

/-- Two programs are observationally equivalent when they reach the same
    final states from every starting state. -/
def ProgEquiv (A B : Program) : Prop :=
  ∀ s t : State, RunsTo (A, s) t ↔ RunsTo (B, s) t

/-- `ProgEquiv` is reflexive. -/
theorem progEquiv_refl (A : Program) : ProgEquiv A A :=
  fun _ _ => Iff.rfl

/-- `ProgEquiv` is symmetric. -/
theorem progEquiv_symm {A B : Program} (h : ProgEquiv A B) : ProgEquiv B A :=
  fun s t => (h s t).symm

/-- `ProgEquiv` is transitive. -/
theorem progEquiv_trans {A B C : Program} (h1 : ProgEquiv A B) (h2 : ProgEquiv B C) :
    ProgEquiv A C :=
  fun s t => (h1 s t).trans (h2 s t)

/-- Equivalent prefixes can be exchanged. -/
theorem progEquiv_append_left {A B : Program} (C : Program) (h : ProgEquiv A B) :
    ProgEquiv (A ++ C) (B ++ C) := by
  intro s t
  constructor
  · intro hr
    rcases runsTo_append_factor (A ++ C, s) t hr A C s rfl with ⟨s', hA, hC⟩
    exact RunsTo_append C s' t ((h s s').mp hA) hC
  · intro hr
    rcases runsTo_append_factor (B ++ C, s) t hr B C s rfl with ⟨s', hB, hC⟩
    exact RunsTo_append C s' t ((h s s').mpr hB) hC

/-- Equivalent suffixes can be exchanged. -/
theorem progEquiv_append_right (A : Program) {B C : Program} (h : ProgEquiv B C) :
    ProgEquiv (A ++ B) (A ++ C) := by
  intro s t
  constructor
  · intro hr
    rcases runsTo_append_factor (A ++ B, s) t hr A B s rfl with ⟨s', hA, hB⟩
    exact RunsTo_append C s' t hA ((h s' t).mp hB)
  · intro hr
    rcases runsTo_append_factor (A ++ C, s) t hr A C s rfl with ⟨s', hA, hC⟩
    exact RunsTo_append B s' t hA ((h s' t).mpr hC)

/-- Incrementing then decrementing the current cell restores the state. -/
theorem incVal_decVal_id (s : State) : s.incVal.decVal = s := by
  cases s with
  | mk ptr tape input output =>
      unfold State.decVal State.incVal State.modifyCell
      congr 1
      funext i
      by_cases h : i = ptr
      · simp only [h, if_pos, Nat.add_sub_cancel]
      · simp only [if_neg h]

/-- `> <` restores the pointer, so it is observationally a no-op. -/
theorem progEquiv_incPtr_decPtr : ProgEquiv [.inc_ptr, .dec_ptr] [] := by
  have hround : ∀ s : State, s.incPtr.decPtr = s := by
    intro s
    simp only [State.incPtr, State.decPtr, add_sub_cancel_right]
  intro s t
  constructor
  · intro h
    have h1 : RunsTo ([Instruction.dec_ptr], s.incPtr) t := runsTo_of_step (by rfl) h
    have h2 : RunsTo (([] : Program), s.incPtr.decPtr) t := runsTo_of_step (by rfl) h1
    rw [hround s] at h2
    exact h2
  · intro h
    rw [runsTo_nil_eq h]
    refine RunsTo.step _ s s.incPtr _ s (by rfl) ?_
    refine RunsTo.step _ s.incPtr s.incPtr.decPtr _ s (by rfl) ?_
    rw [hround s]
    exact RunsTo.halt s

/-- `< >` restores the pointer, so it is observationally a no-op. -/
theorem progEquiv_decPtr_incPtr : ProgEquiv [.dec_ptr, .inc_ptr] [] := by
  have hround : ∀ s : State, s.decPtr.incPtr = s := by
    intro s
    simp only [State.decPtr, State.incPtr, sub_add_cancel]
  intro s t
  constructor
  · intro h
    have h1 : RunsTo ([Instruction.inc_ptr], s.decPtr) t := runsTo_of_step (by rfl) h
    have h2 : RunsTo (([] : Program), s.decPtr.incPtr) t := runsTo_of_step (by rfl) h1
    rw [hround s] at h2
    exact h2
  · intro h
    rw [runsTo_nil_eq h]
    refine RunsTo.step _ s s.decPtr _ s (by rfl) ?_
    refine RunsTo.step _ s.decPtr s.decPtr.incPtr _ s (by rfl) ?_
    rw [hround s]
    exact RunsTo.halt s

/-- `+ -` is a no-op. -/
theorem progEquiv_incVal_decVal : ProgEquiv [.inc_val, .dec_val] [] := by
  intro s t
  constructor
  · intro h
    have h1 : RunsTo ([Instruction.dec_val], s.incVal) t := runsTo_of_step (by rfl) h
    have h2 : RunsTo (([] : Program), s.incVal.decVal) t := runsTo_of_step (by rfl) h1
    rw [incVal_decVal_id s] at h2
    exact h2
  · intro h
    rw [runsTo_nil_eq h]
    refine RunsTo.step _ s s.incVal _ s (by rfl) ?_
    refine RunsTo.step _ s.incVal s.incVal.decVal _ s (by rfl) ?_
    rw [incVal_decVal_id s]
    exact RunsTo.halt s

/-- The mirror image fails: `- +` is not the identity on states. Cell values
    are natural numbers, so decrementing a zero cell truncates and the
    following increment cannot recover it. -/
theorem decVal_incVal_ne_id : ¬ (∀ s : State, s.decVal.incVal = s) := by
  intro h
  have hc := congrArg (fun st => st.tape 0) (h State.mkEmpty)
  simp only [State.decVal, State.incVal, State.modifyCell, State.mkEmpty, if_pos] at hc
  omega

/-- A run that halts after exactly `n` steps witnesses a `RunsTo` chain. This
    is the converse of `run_of_RunsTo`. -/
theorem runsTo_of_runsExactly : ∀ (n : Nat) (prog : Program) (s t : State),
    RunsExactly n prog s t → RunsTo (prog, s) t := by
  intro n
  induction n with
  | zero =>
      intro prog s t h
      have hts : t = s := by
        have hrun := h.1
        simp only [run] at hrun
        exact (Option.some_inj.mp hrun).symm
      have hnil : prog = [] := (stepsToHalt_one_eq_zero prog s).mp h.2
      rw [hts, hnil]
      exact RunsTo.halt s
  | succ k ih =>
      intro prog s t h
      rcases hstep : step prog s with _ | ⟨p', s'⟩
      · exfalso
        have hsteps := h.2
        simp only [stepsToHalt, hstep] at hsteps
        omega
      · have hrest : RunsExactly k p' s' t := by
          constructor
          · have hrun := h.1
            simpa only [run, hstep] using hrun
          · have hsteps := h.2
            simp only [stepsToHalt, hstep, Nat.add_right_cancel_iff] at hsteps
            exact hsteps
        exact RunsTo.step prog s s' p' t hstep (ih p' s' t hrest)

/-- One direction of `progEquiv_loop`, by strong induction on the exact length
    of the halting run. Each iteration costs at least the loop-entry step, so
    the measure strictly decreases. -/
theorem runsTo_loop_of_progEquiv (A B : Program) (h : ProgEquiv A B) :
    ∀ (n : Nat) (s t : State), RunsExactly n [Instruction.loop A] s t →
      RunsTo ([Instruction.loop B], s) t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hex
    by_cases hz : State.currentVal s = 0
    · have hstepA : step [Instruction.loop A] s = some ([], s) := step_loop_zero s A hz
      have hstepB : step [Instruction.loop B] s = some ([], s) := step_loop_zero s B hz
      rcases runsExactly_step n _ s t hex ([] : Program) s hstepA with ⟨m, hm, _⟩
      have hts : t = s := runsTo_nil_eq (runsTo_of_runsExactly m [] s t hm)
      rw [hts]
      exact RunsTo.step _ s s _ s hstepB (RunsTo.halt s)
    · have hstepA : step [Instruction.loop A] s = some (A ++ [Instruction.loop A], s) :=
        step_loop_nonzero s A hz
      have hstepB : step [Instruction.loop B] s = some (B ++ [Instruction.loop B], s) :=
        step_loop_nonzero s B hz
      rcases runsExactly_step n _ s t hex _ s hstepA with ⟨m, hm, hmn⟩
      have hrun : RunsTo (A ++ [Instruction.loop A], s) t :=
        runsTo_of_runsExactly m _ s t hm
      rcases runsTo_append_factor _ t hrun A [Instruction.loop A] s rfl with ⟨s', hA, _⟩
      rcases runsExactly_append_suffix (A, s) s' hA [Instruction.loop A] m t hm with
        ⟨j, hj, hjm⟩
      have hjn : j < n := by omega
      exact RunsTo.step _ s s _ t hstepB
        (RunsTo_append [Instruction.loop B] s' t ((h s s').mp hA) (ih j hjn s' t hj))

/-- Equivalent loop bodies give equivalent loops, so a rewrite is valid inside
    a loop and therefore at any depth of nesting. -/
theorem progEquiv_loop {A B : Program} (h : ProgEquiv A B) :
    ProgEquiv [Instruction.loop A] [Instruction.loop B] := by
  intro s t
  constructor
  · intro hr
    rcases run_of_RunsTo ([Instruction.loop A], s) t hr with ⟨n, hn⟩
    exact runsTo_loop_of_progEquiv A B h n s t hn
  · intro hr
    rcases run_of_RunsTo ([Instruction.loop B], s) t hr with ⟨n, hn⟩
    exact runsTo_loop_of_progEquiv B A (progEquiv_symm h) n s t hn

end LeanBF
