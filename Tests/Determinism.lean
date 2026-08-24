/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Examples.HelloWorld
import LeanBF.Theory.Determinism

/-!
# Determinism Tests

Kernel re-assertions of the determinism theorems on concrete programs: the
step function has at most one successor, runs of a fixed length agree, and
the `Hello World!` output is the unique one reachable.
-/

namespace LeanBF.Tests

open LeanBF

example (c₁ c₂ : Program × State)
    (h₁ : step [.inc_val] State.mkEmpty = some c₁)
    (h₂ : step [.inc_val] State.mkEmpty = some c₂) : c₁ = c₂ :=
  step_deterministic [.inc_val] State.mkEmpty c₁ c₂ h₁ h₂

example (t₁ t₂ : State)
    (h₁ : run 8 [.inc_val, .write, .inc_val, .write] State.mkEmpty = some t₁)
    (h₂ : run 8 [.inc_val, .write, .inc_val, .write] State.mkEmpty = some t₂) : t₁ = t₂ :=
  run_deterministic 8 [.inc_val, .write, .inc_val, .write] State.mkEmpty t₁ t₂ h₁ h₂

example (t₁ t₂ : State)
    (h₁ : RunsTo ([.inc_val, .write], State.mkEmpty) t₁)
    (h₂ : RunsTo ([.inc_val, .write], State.mkEmpty) t₂) : t₁ = t₂ :=
  runsTo_deterministic ([.inc_val, .write], State.mkEmpty) t₁ t₂ h₁ h₂

/-- Any halting run of `Hello World!` produces the verified output. -/
example (t : State) (h : RunsTo (Examples.helloWorld, Examples.helloState) t)
    (t' : State) (h' : RunsTo (Examples.helloWorld, Examples.helloState) t') :
    t.output = t'.output :=
  runsTo_output_deterministic Examples.helloWorld Examples.helloState t t' h h'

/-- Echoing a fixed input stream yields a unique output. -/
example (t₁ t₂ : State)
    (h₁ : RunsTo ([.read, .write], { State.mkEmpty with input := [7, 8] }) t₁)
    (h₂ : RunsTo ([.read, .write], { State.mkEmpty with input := [7, 8] }) t₂) :
    t₁.output = t₂.output :=
  runsTo_output_function [.read, .write] [7, 8] t₁ t₂ h₁ h₂

end LeanBF.Tests
