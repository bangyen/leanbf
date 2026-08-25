/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Semantics
import LeanBF.Theory.Semantics

/-!
# Semantics Tests

Kernel re-assertions of the `LeanBF.Core.Semantics` definitions and the
`LeanBF.Theory.Semantics` lemmas.
-/

namespace LeanBF.Tests

open LeanBF

example : step [] State.mkEmpty = none :=
  rfl

example : step [.inc_val] State.mkEmpty = some ([], State.incVal State.mkEmpty) :=
  rfl

example : step [.write] State.mkEmpty = some ([], { State.mkEmpty with output := [0] }) :=
  rfl

example : RunsTo ([], State.mkEmpty) State.mkEmpty :=
  RunsTo.halt State.mkEmpty

example : step [.inc_ptr] State.mkEmpty = some ([], State.incPtr State.mkEmpty) :=
  step_incPtr State.mkEmpty

example (s : State) (body : Program) (h : State.currentVal s = 0) :
    step [.loop body] s = some ([], s) :=
  step_loop_zero s body h

example (s : State) : step [.dec_ptr] s = some ([], s.decPtr) :=
  step_decPtr s

example (s : State) : step [.inc_val] s = some ([], s.incVal) :=
  step_incVal s

example (s : State) : step [.dec_val] s = some ([], s.decVal) :=
  step_decVal s

example (s : State) (h : s.input = []) :
    step [.read] s = some ([], { s with tape := fun i => if i = s.ptr then 0 else s.tape i }) :=
  step_read_nil s h

example (s : State) (x : Nat) (xs : List Nat) (h : s.input = x :: xs) :
    step [.read] s =
      some ([], { s with tape := fun i => if i = s.ptr then x else s.tape i, input := xs }) :=
  step_read_cons s x xs h

example (s : State) : step [.write] s = some ([], { s with output := s.currentVal :: s.output }) :=
  step_write s

example (s : State) : halts [] s :=
  halts_empty s

example (s : State) (h : 0 < s.tape s.ptr) : ¬ halts [.loop [.inc_val]] s :=
  loop_incVal_never_halts s h

example (s : State) (x : Nat) (xs : List Nat) (h : s.input = x :: xs) :
    (runSeq [.read, .write] s).output = x :: s.output ∧ (runSeq [.read, .write] s).input = xs :=
  read_write_echo s x xs h

example (s : State) :
    (runSeq [.write, .write] s).output = State.currentVal s :: State.currentVal s :: s.output :=
  runSeq_write_write_output s

example (s : State) (k : Nat) (hk : k ≤ s.input.length) :
    (runSeq (List.replicate k .read) s).input = s.input.drop k :=
  runSeq_read_input s k hk

/-- A run only extends the output; the output is stored most recent first, so
    the extension is a prepend. -/
example (cfg : Program × State) (t : State) (h : RunsTo cfg t) :
    ∃ w, t.output = w ++ cfg.2.output :=
  runsTo_output_extends cfg t h

/-- A run's reads consume a prefix of the input. -/
example (cfg : Program × State) (t : State) (h : RunsTo cfg t) :
    ∃ v, cfg.2.input = v ++ t.input :=
  runsTo_input_suffix cfg t h

/-- On a concrete echo program `, . , .` the input is consumed and the two
    reads are echoed to the output. -/
example : (run 10 [.read, .write, .read, .write]
    { State.mkEmpty with input := [3, 7] }).map (fun s => (s.input, s.output))
    = some ([], [7, 3]) := by
  decide

/-- Reading past end-of-input pushes `0` and leaves the input empty. -/
example : (run 10 [.read, .write] State.mkEmpty).map (fun s => (s.input, s.output))
    = some ([], [0]) := by
  decide

end LeanBF.Tests
