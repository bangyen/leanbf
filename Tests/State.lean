/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.State
import LeanBF.Theory.State

/-!
# State Tests

Kernel re-assertions of the `LeanBF.Core.State` definitions and the
`LeanBF.Theory.State` lemmas.
-/

namespace LeanBF.Tests

open LeanBF

example : State.ptr State.mkEmpty = 0 :=
  rfl

example : State.input State.mkEmpty = [] :=
  rfl

example : State.output State.mkEmpty = [] :=
  rfl

example : State.currentVal State.mkEmpty = 0 :=
  rfl

example : State.incPtr State.mkEmpty = { State.mkEmpty with ptr := 1 } :=
  rfl

example : State.currentVal (State.incVal State.mkEmpty) = 1 :=
  rfl

example : State.currentVal (State.incVal State.mkEmpty) =
    State.currentVal State.mkEmpty + 1 :=
  currentVal_incVal State.mkEmpty

example : State.currentVal (State.decVal (State.incVal State.mkEmpty)) =
    State.currentVal State.mkEmpty :=
  currentVal_incVal_decVal State.mkEmpty

example (s : State) (f : Nat → Nat) :
    State.currentVal (State.modifyCell s f) = f (State.currentVal s) :=
  currentVal_modifyCell s f

end LeanBF.Tests
