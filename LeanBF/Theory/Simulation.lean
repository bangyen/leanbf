/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Compiler
import LeanBF.Core.Semantics
import LeanBF.Theory.Completeness
import LeanBF.Theory.Loop
import LeanBF.Theory.Semantics

/-!
# The Simulation

Infrastructure for the completeness proof: a fuel-capped runner whose
results convert into `RunsTo` chains, and the first concrete simulation —
the compiled empty program halts from any simulating state.

## Main definitions

* `runToCompletion`: Run until the program halts or the fuel runs out.

## Theorems

* `step_none_iff_empty`: The step relation is undefined exactly on the empty
  program.
* `runsTo_halt_of_step_none`: An undefined step means the program halts.
* `runsTo_of_runToCompletion_some`: A completed fuel-capped run gives a
  RunsTo chain.
* `runToCompletion_some_of_haltsWithin`: A program that halts within `n`
  steps is finished by `runToCompletion n`.
* `RunsTo_of_haltsWithin`: A program that halts within `n` steps reaches the
  empty program.
* `compile_empty_haltsWithin`: The compiled empty program halts within 100
  steps from any simulating state.
* `compile_empty_halts`: The compiled empty program halts.
* `compile_empty_simulates`: The empty Minsky program is simulated by its
  compilation.
* `RunsTo_append`: RunsTo composes across concatenation.
* `runToCompletion_succ_eq`: Extra fuel after termination does not change a
  completed run.
* `runToCompletion_eq_of_ge`: Completing within `n` steps means completing
  within any larger bound.
-/

namespace LeanBF

/--
Run until the program halts (its instruction list is empty) or the fuel runs
out, whichever comes first.
-/
def runToCompletion (fuel : ℕ) (prog : Program) (s : State) : Option State :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match step prog s with
    | none => some s
    | some (prog', s') => runToCompletion fuel prog' s'

/-- The step relation is undefined exactly on the empty program. -/
theorem step_none_iff_empty (prog : Program) (s : State) :
    step prog s = none ↔ prog = [] := by
  constructor
  · intro h
    cases prog with
    | nil => rfl
    | cons i rest => exact False.elim (step_cons_ne_none i rest s h)
  · intro h
    rw [h]
    rfl

/-- An undefined step means the program halts. -/
theorem runsTo_halt_of_step_none (prog : Program) (s : State) (h : step prog s = none) :
    RunsTo (prog, s) s := by
  have hprog : prog = [] := (step_none_iff_empty prog s).mp h
  rw [hprog]
  exact RunsTo.halt s

/-- A completed fuel-capped run gives a `RunsTo` chain. -/
theorem runsTo_of_runToCompletion_some (fuel : ℕ) (prog : Program) (s : State) :
    (∃ s' : State, runToCompletion fuel prog s = some s') →
      ∃ s' : State, RunsTo (prog, s) s' := by
  induction fuel generalizing prog s with
  | zero =>
      intro h
      rcases h with ⟨s', h'⟩
      simp only [runToCompletion] at h'
      cases h'
  | succ fuel ih =>
      intro h
      cases hstep : step prog s with
      | none =>
          exact ⟨s, runsTo_halt_of_step_none prog s hstep⟩
      | some cfg =>
          rcases h with ⟨s', h'⟩
          simp only [runToCompletion, hstep] at h'
          have ih' := ih cfg.1 cfg.2
          rcases ih' ⟨s', h'⟩ with ⟨s_final, h_final⟩
          exact ⟨s_final, RunsTo.step prog s cfg.2 cfg.1 s_final hstep h_final⟩

/-- A program that halts within `n` steps is finished by `runToCompletion n`. -/
theorem runToCompletion_some_of_haltsWithin (n : ℕ) (prog : Program) (s : State) :
    haltsWithin n prog s → ∃ s' : State, runToCompletion n prog s = some s' := by
  induction n generalizing prog s with
  | zero =>
      intro h
      simp only [haltsWithin, stepsToHalt] at h
      cases h
  | succ n ih =>
      intro h
      unfold haltsWithin stepsToHalt at h
      cases hstep : step prog s with
      | none =>
          exact ⟨s, by simp only [runToCompletion, hstep]⟩
      | some cfg =>
          have hlt : stepsToHalt n cfg.1 cfg.2 < n := by
            have : stepsToHalt n cfg.1 cfg.2 + 1 < n + 1 := by
              simpa only [hstep, Nat.succ_eq_add_one] using h
            exact Nat.succ_lt_succ_iff.mp (by simpa only [Nat.succ_eq_add_one] using this)
          have ih' := ih cfg.1 cfg.2
          rcases ih' hlt with ⟨s', h'⟩
          exact ⟨s', by simp only [runToCompletion, hstep, h']⟩

/-- A program that halts within `n` steps reaches the empty program. -/
theorem RunsTo_of_haltsWithin (n : ℕ) (prog : Program) (s : State) :
    haltsWithin n prog s → ∃ s' : State, RunsTo (prog, s) s' := by
  intro h
  exact runsTo_of_runToCompletion_some n prog s (runToCompletion_some_of_haltsWithin n prog s h)

/-- The compiled empty program halts within 100 steps from any simulating
    state. -/
theorem compile_empty_haltsWithin (ms : Minsky.State) :
    haltsWithin 100 (Compiler.compileProgram ([] : Minsky.Program)) (simState ms) := by
  unfold haltsWithin
  rw [show
    stepsToHalt 100 (Compiler.compileProgram ([] : Minsky.Program)) (simState ms) = 74 by rfl]
  decide

/-- The compiled empty program halts. -/
theorem compile_empty_halts (ms : Minsky.State) :
    halts (Compiler.compileProgram ([] : Minsky.Program)) (simState ms) :=
  ⟨100, compile_empty_haltsWithin ms⟩

/-- The empty Minsky program is simulated by its compilation. -/
theorem compile_empty_simulates (ms : Minsky.State) :
    ∃ s' : State, RunsTo (Compiler.compileProgram ([] : Minsky.Program), simState ms) s' :=
  RunsTo_of_haltsWithin 100 _ _ (compile_empty_haltsWithin ms)

/-- Extra fuel after termination does not change a completed run. -/
theorem runToCompletion_succ_eq (n : Nat) (prog : Program) (s : State)
    (hterm : runToCompletion n prog s ≠ none) :
    runToCompletion (n + 1) prog s = runToCompletion n prog s := by
  induction n generalizing prog s with
  | zero => simp only [runToCompletion] at hterm; exact False.elim (hterm rfl)
  | succ n ih =>
      cases hstep : step prog s with
      | none => simp only [runToCompletion, hstep]
      | some cfg =>
          have hterm' : runToCompletion n cfg.1 cfg.2 ≠ none := by
            intro h'
            apply hterm
            rw [runToCompletion, hstep]
            exact h'
          have hstep' :
              runToCompletion (n + 1 + 1) prog s = runToCompletion (n + 1) cfg.1 cfg.2 := by
            rw [runToCompletion, hstep]
          have hstep'' : runToCompletion (n + 1) prog s = runToCompletion n cfg.1 cfg.2 := by
            rw [runToCompletion, hstep]
          rw [hstep', hstep'']
          rw [ih cfg.1 cfg.2 hterm']

/-- Completing within `n` steps means completing within any larger bound. -/
theorem runToCompletion_eq_of_ge (n k : Nat) (prog : Program) (s : State)
    (hterm : runToCompletion n prog s ≠ none) :
    runToCompletion (n + k) prog s = runToCompletion n prog s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hle : runToCompletion (n + k) prog s ≠ none := by
        intro h'
        apply hterm
        rw [ih] at h'
        exact h'
      rw [← Nat.add_assoc]
      rw [runToCompletion_succ_eq (n + k) prog s hle]
      exact ih
theorem RunsTo_append {cfg : Program × State} (B : Program) (s' s'' : State)
    (h1 : RunsTo cfg s') (h2 : RunsTo (B, s') s'') :
    RunsTo (cfg.1 ++ B, cfg.2) s'' := by
  revert h2
  induction h1 with
  | halt s =>
      intro h2
      simpa only using h2
  | step p s s1 p' s_final hstep hrest ih =>
      intro h2
      exact RunsTo.step (p ++ B) s s1 (p' ++ B) s''
        (step_append p B s s1 p' hstep) (ih h2)

end LeanBF
