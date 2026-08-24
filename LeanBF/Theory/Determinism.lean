/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics
import LeanBF.Theory.Semantics

/-!
# Determinism

The interpreter is deterministic: `step` is a total function, so a
configuration has at most one successor, at most one halting state is
reachable from it, and the state after `n` steps is unique. Consequently a
program is a function from its input stream to its output stream.

## Theorems

* `step_deterministic`: A configuration has at most one successor.
* `run_deterministic`: The state after `n` steps is unique.
* `runsTo_deterministic`: At most one halting state is reachable.
* `runsTo_output_deterministic`: The output of a halting run is unique.
* `runsTo_output_function`: A program is a function from input to output.
-/

namespace LeanBF

/-- A configuration has at most one successor: `step` is a function, so two
    successors of the same configuration are equal. -/
theorem step_deterministic (prog : Program) (s : State) (c₁ c₂ : Program × State)
    (h₁ : step prog s = some c₁) (h₂ : step prog s = some c₂) : c₁ = c₂ :=
  Option.some_inj.mp (h₁ ▸ h₂)

/-- The state after `n` steps is unique: `run` is a function, giving a
    run-level confluence statement. -/
theorem run_deterministic (n : ℕ) (prog : Program) (s : State) (t₁ t₂ : State)
    (h₁ : run n prog s = some t₁) (h₂ : run n prog s = some t₂) : t₁ = t₂ :=
  Option.some_inj.mp (h₁ ▸ h₂)

/-- At most one halting state is reachable from a configuration. The step
    relation is the graph of a partial function, so the reflexive-transitive
    closure relates each configuration to at most one halting state. -/
theorem runsTo_deterministic : ∀ (c : Program × State) (t₁ t₂ : State),
    RunsTo c t₁ → RunsTo c t₂ → t₁ = t₂ := by
  intro c t₁ t₂ h₁
  induction h₁ with
  | halt s =>
      intro h₂
      cases h₂ with
      | halt => rfl
      | step _ _ _ _ _ hstep _ => exact absurd hstep (by simp only [step_empty]; simp)
  | step p s s' p' s_final hstep _ ih =>
      intro h₂
      cases h₂ with
      | halt => exact absurd hstep (by simp only [step_empty]; simp)
      | step _ _ s'' p'' _ hstep₂ hrest₂ =>
          have hpair : (p', s') = (p'', s'') :=
            step_deterministic p s (p', s') (p'', s'') hstep hstep₂
          rw [← hpair] at hrest₂
          exact ih hrest₂

/-- The output of a halting run is unique: two halting runs of the same
    program from the same state produce the same output stream. -/
theorem runsTo_output_deterministic (prog : Program) (s : State) (t₁ t₂ : State)
    (h₁ : RunsTo (prog, s) t₁) (h₂ : RunsTo (prog, s) t₂) : t₁.output = t₂.output := by
  have h : t₁ = t₂ := runsTo_deterministic (prog, s) t₁ t₂ h₁ h₂
  rw [h]

/-- A program is a function from its input stream to its output stream: run
    on a fixed input from the empty tape, every halting run produces the same
    output. -/
theorem runsTo_output_function (prog : Program) (input : List Nat) (t₁ t₂ : State)
    (h₁ : RunsTo (prog, { State.mkEmpty with input := input }) t₁)
    (h₂ : RunsTo (prog, { State.mkEmpty with input := input }) t₂) :
    t₁.output = t₂.output :=
  runsTo_output_deterministic prog { State.mkEmpty with input := input } t₁ t₂ h₁ h₂

end LeanBF
