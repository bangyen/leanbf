/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Register

/-!
# Register Machine Traces

Reachability counted by steps, and what that buys.

`Reaches` and `RunsTo` are `Prop`-valued inductives, so a derivation carries
no number: there is no way to ask how many steps it took, and therefore no
way to induct on that number. Every fragment proved so far only ever needed
to exhibit a path, so this never came up. The universal machine's halting
argument does need it. Showing that a machine which halts must have halted
*through* the success branch means ruling out every other way it could have
stopped, and that is an induction on the length of the halting trace.

`runFor` supplies the number. It iterates `step` a fixed number of times,
returning `none` if the machine stops early, and `reaches_iff_runFor` says it
agrees with `Reaches`.

The step relation is a function, so a state has one successor and a trace has
no branch points. `runsTo_of_reaches` is where that gets used: if a machine
halts, and some fragment is known to walk from the start to an intermediate
state, then the halting run passes through that state. A forward-only lemma
about where a fragment goes becomes a fact about where the whole run must
have been.

## Main definitions

* `runFor`: Iterating the step relation a fixed number of times.

## Theorems

* `runFor_add`: Splitting an iteration at an intermediate count.
* `reaches_of_runFor`: A completed iteration gives a reachability.
* `runFor_of_reaches`: A reachability gives a completed iteration.
* `reaches_iff_runFor`: Reachability is iteration for some count.
* `runsTo_of_reaches`: A halting run passes through everything reachable on
  the way.
* `runsTo_of_reaches_halt`: Reaching a terminal state is a halting run.
* `runsTo_of_reaches_runsTo`: Prefixing a halting run with a reachability.
* `runsTo_terminal`: A halting run ends where the machine has no successor.
* `runsTo_runFor`: A halting run is an iteration onto a terminal state.
* `runFor_pos_of_step`: A first step and a path make a positive count.
* `runFor_pos_of_reaches`: A path out of a state that can step is positive.
* `no_runsTo_of_steps`: A machine that always takes at least one more step
  never halts.
* `no_runsTo_of_diverges`: The same, when consecutive stages differ.
-/

namespace LeanBF

namespace Register

/-- Iterate the step relation `n` times, or `none` if the machine stops
    before the count is reached. -/
def runFor (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => match step p s with
    | none => none
    | some s' => runFor p n s'

theorem runFor_add (p : Program) (m n : Nat) (s t : State) (h : runFor p m s = some t) :
    runFor p (m + n) s = runFor p n t := by
  induction m generalizing s with
  | zero =>
      simp only [runFor, Option.some.injEq] at h
      rw [h, Nat.zero_add]
  | succ k ih =>
      rw [show k + 1 + n = k + n + 1 by omega]
      simp only [runFor] at h ⊢
      cases hstep : step p s with
      | none =>
          rw [hstep] at h
          exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
      | some s' =>
          rw [hstep] at h
          simp only []
          exact ih s' h

theorem reaches_of_runFor (p : Program) : ∀ (n : Nat) (s t : State),
    runFor p n s = some t → Reaches p s t := by
  intro n
  induction n with
  | zero =>
      intro s t h
      simp only [runFor, Option.some.injEq] at h
      rw [h]
      exact Reaches.refl _
  | succ k ih =>
      intro s t h
      simp only [runFor] at h
      cases hstep : step p s with
      | none => rw [hstep] at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
      | some s' =>
          rw [hstep] at h
          exact Reaches.step s s' t hstep (ih s' t h)

theorem runFor_of_reaches (p : Program) (s t : State) (h : Reaches p s t) :
    ∃ n, runFor p n s = some t := by
  induction h with
  | refl s => exact ⟨0, rfl⟩
  | step s s' t hstep _ ih =>
      rcases ih with ⟨n, hn⟩
      exact ⟨n + 1, by simp only [runFor, hstep]; exact hn⟩

theorem reaches_iff_runFor (p : Program) (s t : State) :
    Reaches p s t ↔ ∃ n, runFor p n s = some t :=
  ⟨runFor_of_reaches p s t, fun ⟨n, hn⟩ => reaches_of_runFor p n s t hn⟩

/-- A halting run passes through everything reachable on the way. The step
    relation is a function, so the run from a state is unique; a fragment
    known to walk from `s` to `s'` therefore describes a prefix of any
    halting run out of `s`, and the rest of that run starts at `s'`. -/
theorem runsTo_of_reaches (p : Program) (s s' t : State)
    (hr : Reaches p s s') (hrt : RunsTo p s t) : RunsTo p s' t := by
  induction hr with
  | refl s => exact hrt
  | step a b c hstep _ ih =>
      cases hrt with
      | halt _ hterm =>
          -- A terminal state has no successor, contradicting the step taken.
          exfalso
          rcases hterm with hh | hn
          · rw [step, hh] at hstep
            simp only [reduceCtorEq] at hstep
          · rw [step, hn] at hstep
            simp only [reduceCtorEq] at hstep
      | step _ b' _ hstep' hrest =>
          rw [hstep] at hstep'
          have hbb : b = b' := by
            injection hstep'
          exact ih (by rwa [← hbb] at hrest)

/-- Reaching a terminal state is a halting run. This is how a fragment's
    forward path becomes a `RunsTo` once it lands on a `halt`. -/
theorem runsTo_of_reaches_halt (p : Program) (s t : State) (hr : Reaches p s t)
    (hterm : (p : List Instruction)[t.pc]? = some Instruction.halt ∨
      (p : List Instruction)[t.pc]? = none) : RunsTo p s t := by
  induction hr with
  | refl u => exact RunsTo.halt u hterm
  | step a b c hstep _ ih => exact RunsTo.step a b c hstep (ih hterm)

/-- Prefixing a halting run with a reachability. `runsTo_of_reaches` cuts a
    known prefix off a halting run; this glues one back on, which is what
    turns a fragment's forward path into a halting run of the whole
    machine. -/
theorem runsTo_of_reaches_runsTo (p : Program) (s a t : State)
    (hr : Reaches p s a) (ht : RunsTo p a t) : RunsTo p s t := by
  induction hr with
  | refl _ => exact ht
  | step u v _ hstep _ ih => exact RunsTo.step u v _ hstep (ih ht)

/-- A halting run ends where the machine has no successor. The `RunsTo`
    constructors phrase termination as a condition on the program slot; this
    restates it as `step` returning nothing, which is the form the counting
    argument compares against. -/
theorem runsTo_terminal (p : Program) (s t : State) (h : RunsTo p s t) :
    step p t = none := by
  induction h with
  | halt u hterm =>
      rcases hterm with hh | hn
      · rw [step, hh]
      · rw [step, hn]
  | step _ _ _ _ _ ih => exact ih

/-- A halting run is an iteration of some exact length landing on a state
    with no successor. This is the numeric form of halting the counting
    argument needs: a bound on how long the machine can still be running. -/
theorem runsTo_runFor (p : Program) (s t : State) (h : RunsTo p s t) :
    ∃ n, runFor p n s = some t ∧ step p t = none := by
  induction h with
  | halt u hterm =>
      refine ⟨0, rfl, ?_⟩
      rcases hterm with hh | hn
      · rw [step, hh]
      · rw [step, hn]
  | step u v _ hstep _ ih =>
      rcases ih with ⟨n, hn, hterm⟩
      exact ⟨n + 1, by simp only [runFor, hstep]; exact hn, hterm⟩

/-- A first step followed by a path is a run of positive length. The
    fragment lemmas produce a bare `Reaches`, which carries no count, and
    `runFor_of_reaches` supplies one with no guarantee it is positive.
    Exhibiting the first step separately is what makes it so, and every
    block begins with an instruction that executes unconditionally. -/
theorem runFor_pos_of_step (p : Program) (s s₁ s' : State)
    (hstep : step p s = some s₁) (hr : Reaches p s₁ s') :
    ∃ c, 1 ≤ c ∧ runFor p c s = some s' := by
  rcases runFor_of_reaches p _ _ hr with ⟨d, hd⟩
  refine ⟨d + 1, by omega, ?_⟩
  rw [show d + 1 = 1 + d by omega, runFor_add p 1 d s s₁ (by simp only [runFor, hstep])]
  exact hd

/-- A path that moves the program counter takes at least one step. The
    fragment lemmas hand back a bare `Reaches` whose target is a computed
    term, which resists case analysis; comparing the two counters settles the
    length without any, and a block always exits somewhere other than the
    address it was entered at. -/
theorem runFor_pos_of_reaches (p : Program) (s s' : State)
    (hpc : s.pc ≠ s'.pc) (hr : Reaches p s s') :
    ∃ c, 1 ≤ c ∧ runFor p c s = some s' := by
  rcases runFor_of_reaches p _ _ hr with ⟨d, hd⟩
  refine ⟨d, ?_, hd⟩
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · -- A zero-length path ends where it began, counter included.
    simp only [runFor, Option.some.injEq] at hd
    exact absurd (congrArg State.pc hd) hpc
  · exact hpos

/-- A machine that always has at least one more step to take never halts.

    `inv` enumerates states the machine passes through, each reached from the
    last by a positive number of steps. So `inv n` is at least `n` steps
    along, and the machine is still running there. A halting run would be an
    iteration of some fixed length `n` onto a state with no successor; taking
    the sequence `n + 1` stages out contradicts it, the run being over by
    then.

    The step count is explicit rather than inferred from consecutive stages
    differing. A machine can step without changing state — a `jzdec` on an
    empty register naming its own address does exactly that — so the two
    formulations are not interchangeable, and only this one is available to a
    caller whose stages are not obviously distinct. -/
theorem no_runsTo_of_steps (p : Program) (inv : Nat → State)
    (hstep : ∀ j, ∃ c, 1 ≤ c ∧ runFor p c (inv j) = some (inv (j + 1)))
    (t : State) : ¬ RunsTo p (inv 0) t := by
  intro hrun
  rcases runsTo_runFor p _ t hrun with ⟨n, hn, hterm⟩
  -- Each stage costs at least one step, so `inv j` is `j` or more steps out.
  have hcount : ∀ j, ∃ c, j ≤ c ∧ runFor p c (inv 0) = some (inv j) := by
    intro j
    induction j with
    | zero => exact ⟨0, le_refl _, rfl⟩
    | succ i ih =>
        rcases ih with ⟨c, hci, hc⟩
        rcases hstep i with ⟨d, hd1, hd⟩
        exact ⟨c + d, by omega, by rw [runFor_add p c d _ _ hc]; exact hd⟩
  rcases hcount (n + 1) with ⟨c, hcn, hc⟩
  -- The run is over after `n` steps, but the sequence is still going at `c`.
  rw [show c = n + (c - n) by omega, runFor_add p n _ _ _ hn] at hc
  cases hcd : c - n with
  | zero => omega
  | succ e =>
      rw [hcd] at hc
      simp only [runFor, hterm, reduceCtorEq] at hc

/-- A machine with somewhere further to go at every stage never halts, when
    consecutive stages are known to differ. The difference supplies the
    positive step count `no_runsTo_of_steps` asks for: a reachability of no
    steps would leave the state where it was. -/
theorem no_runsTo_of_diverges (p : Program) (inv : Nat → State)
    (hstep : ∀ j, Reaches p (inv j) (inv (j + 1)))
    (hne : ∀ j, inv j ≠ inv (j + 1)) (t : State) : ¬ RunsTo p (inv 0) t := by
  refine no_runsTo_of_steps p inv (fun j => ?_) t
  rcases runFor_of_reaches p _ _ (hstep j) with ⟨d, hd⟩
  refine ⟨d, ?_, hd⟩
  -- A zero-step move would make the two stages the same state.
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp only [runFor, Option.some.injEq] at hd
    exact absurd hd (hne j)
  · exact hpos

end Register

end LeanBF
