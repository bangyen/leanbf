/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Undecidable

/-!
# Undecidability Tests

Kernel re-assertions of the capstone: one fixed Brainfuck program whose
halting decides every recursive code's, and the conclusion drawn from it.
-/

namespace LeanBF.Tests

open LeanBF LeanBF.Register

/-- A Minsky program whose halting on a power of two decides any code. -/
example : ∃ (M : Minsky.Program), ∀ (c n : Nat),
    (∃ u, Minsky.RunsTo M { pc := 0, c1 := 2 ^ Nat.pair c n, c2 := 0 } u) ↔
      (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code c) n).Dom :=
  universal_minsky

/-- The same, compiled to Brainfuck. The program is fixed; only the starting
    tape varies, and it varies computably in the code and the input. -/
example : ∃ (B : Program), ∀ (c n : Nat),
    halts B (simState { pc := 0, c1 := 2 ^ Nat.pair c n, c2 := 0 }) ↔
      (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code c) n).Dom :=
  universal_brainfuck

/-- The halting problem, restated over code numbers rather than codes, which
    is the form a reduction building a machine input can use. -/
example (n : Nat) : ¬ ComputablePred (fun c : Nat =>
    ((Denumerable.ofNat Nat.Partrec.Code c).eval n).Dom) := halting_problem_nat n

/-- And the conclusion: no computable predicate decides whether the universal
    program halts on a given input. -/
example : ∃ B : Program, ¬ ComputablePred (fun m : Nat =>
    halts B (simState { pc := 0, c1 := 2 ^ m, c2 := 0 })) :=
  brainfuck_halting_undecidable

end LeanBF.Tests
