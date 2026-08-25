/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Universal.Search

/-!
# Step-Bounded Evaluator Tests

Kernel re-assertions that the interpreter a register machine has to run is an
ordinary primitive recursive function of numbers, and that its encoding makes
the search's test a single instruction.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- The interpreter is primitive recursive in all three arguments, the code
    number included. That is what keeps the seven cases from being redone
    over `Nat.Partrec.Code`. -/
example : Nat.Primrec evalnPacked := evalnPacked_primrec

/-- So a register machine already computes it. -/
example : RegComputable evalnPacked := evalnPacked_regComputable

/-- The encoding puts `none` at zero, which is what a `jzdec` tests. -/
example : Encodable.encode (Option.none : Option Nat) = 0 := rfl

/-- And `some x` one above `x`, so the same instruction's decrement decodes
    the answer it just detected. -/
example : Encodable.encode (Option.some 7 : Option Nat) = 8 := rfl

/-- Some bound succeeds exactly when the code halts, which is what the
    search's correctness is measured against. -/
example (c n : Nat) :
    (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code c) n).Dom ↔
      ∃ k, evalnPacked (Nat.pair k (Nat.pair c n)) ≠ 0 :=
  evalnPacked_dom_iff c n

/-- A nonzero result carries the answer one above it. -/
example (k c n x : Nat) :
    evalnPacked (Nat.pair k (Nat.pair c n)) = x + 1 ↔
      Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code c) n = Option.some x :=
  evalnPacked_eq_succ_iff k c n x

end LeanBF.Tests
