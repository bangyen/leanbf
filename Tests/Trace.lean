/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Trace

/-!
# Trace Tests

Kernel re-assertions of the counted iteration and of the factoring that makes
a forward-only fragment lemma say something about a halting run.

## Main definitions

* `twoStep`: Two increments followed by `halt`.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- Increment register `0` twice, then halt. -/
def twoStep : Program := [.inc 0 1, .inc 0 2, .halt]

/-- Counting the steps of a concrete run: two steps land on the halt with
    the register raised twice. -/
example : (runFor twoStep 2 { pc := 0, regs := fun _ => 0 }).map
    (fun s => (s.pc, s.regs 0)) = some (2, 2) := rfl

/-- Iterating past the halt yields nothing. -/
example : runFor twoStep 3 { pc := 0, regs := fun _ => 0 } = none := rfl

/-- Reachability and counted iteration agree. -/
example (p : Program) (s t : State) : Reaches p s t ↔ ∃ n, runFor p n s = some t :=
  reaches_iff_runFor p s t

/-- Splitting an iteration at an intermediate count. -/
example (p : Program) (m n : Nat) (s t : State) (h : runFor p m s = some t) :
    runFor p (m + n) s = runFor p n t :=
  runFor_add p m n s t h

/-- The factoring lemma: a halting run passes through everything reachable on
    the way, which is what turns a fragment's forward path into a constraint
    on how the whole run can have halted. -/
example (p : Program) (s s' t : State) (hr : Reaches p s s') (hrt : RunsTo p s t) :
    RunsTo p s' t :=
  runsTo_of_reaches p s s' t hr hrt

end LeanBF.Tests
