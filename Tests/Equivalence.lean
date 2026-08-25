/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Equivalence

/-!
# Program Equivalence Tests

Kernel re-assertions of `ProgEquiv`: the equivalence-relation laws, the
congruence rules for `++`, and the cancellation instances.
-/

namespace LeanBF.Tests

open LeanBF

example : ProgEquiv [.inc_ptr, .dec_ptr] [] :=
  progEquiv_incPtr_decPtr

example : ProgEquiv [.dec_ptr, .inc_ptr] [] :=
  progEquiv_decPtr_incPtr

example : ProgEquiv [.inc_val, .dec_val] [] :=
  progEquiv_incVal_decVal

example : ¬ (∀ s : State, s.decVal.incVal = s) :=
  decVal_incVal_ne_id

/-- Cancellation applies inside a larger program: the `> <` in the middle of
    `. > < .` can be deleted. -/
example : ProgEquiv ([.write] ++ [.inc_ptr, .dec_ptr] ++ [.write])
    ([.write] ++ [] ++ [.write]) :=
  progEquiv_append_right [.write]
    (progEquiv_append_left [.write] progEquiv_incPtr_decPtr)

/-- Equivalence is symmetric and transitive, so cancellations chain. -/
example : ProgEquiv [.inc_ptr, .dec_ptr] [.inc_val, .dec_val] :=
  progEquiv_trans progEquiv_incPtr_decPtr (progEquiv_symm progEquiv_incVal_decVal)

/-- A run of `A ++ C` factors through a halting state of `A`. -/
example (A C : Program) (s t : State) (h : RunsTo (A ++ C, s) t) :
    ∃ s', RunsTo (A, s) s' ∧ RunsTo (C, s') t :=
  runsTo_append_factor (A ++ C, s) t h A C s rfl

/-- The empty program's runs end where they start. -/
example (s t : State) (h : RunsTo (([] : Program), s) t) : t = s :=
  runsTo_nil_eq h

/-- Equivalent bodies give equivalent loops. -/
example : ProgEquiv [.loop [.inc_ptr, .dec_ptr]] [.loop []] :=
  progEquiv_loop progEquiv_incPtr_decPtr

/-- Congruence composes, so a rewrite applies inside nested loops. -/
example : ProgEquiv [.loop [.loop [.inc_val, .dec_val]]] [.loop [.loop []]] :=
  progEquiv_loop (progEquiv_loop progEquiv_incVal_decVal)

/-- Loop congruence combines with the append rules. -/
example : ProgEquiv ([.write] ++ [.loop [.inc_val, .dec_val]])
    ([.write] ++ [.loop []]) :=
  progEquiv_append_right [.write] (progEquiv_loop progEquiv_incVal_decVal)

/-- An exact run witnesses a `RunsTo` chain. -/
example (prog : Program) (s t : State) (n : Nat) (h : RunsExactly n prog s t) :
    RunsTo (prog, s) t :=
  runsTo_of_runsExactly n prog s t h

end LeanBF.Tests
