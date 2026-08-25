/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Universal.Primrec

/-!
# The Step-Bounded Evaluator as a Register Machine

What the outer search will run at each candidate bound.

`Nat.Partrec.Code.eval` need not terminate, so no total fragment computes it.
`evaln` is the step-indexed alternative, and `primrec_evaln` says it is
primitive recursive *in all three of its arguments*, the code number
included. That is the fact that keeps the seven cases from having to be
redone over `Nat.Partrec.Code`: the interpreter is itself an ordinary
primitive recursive function of numbers, so `primrec_regComputable` already
supplies a machine for it.

Everything below is a total function of one number. The three arguments are
packed with `Nat.pair`, the same pairing the fragments compute, and the
`Option` result is encoded as `0` for `none` and `x + 1` for `some x` —
which is what `Encodable.encode` already does on `Option ℕ`, so no separate
coding has to be defined or proved.

That encoding is also what makes the search's test free. The register machine
branches by `jzdec`, which jumps when a register is zero and *decrements*
otherwise; on a `some x` result that decrement turns `x + 1` into `x`, so the
same instruction that detects success also decodes it.

## Main definitions

* `evalnPacked`: The step-bounded evaluator on one packed, encoded argument.

## Theorems

* `evalnPacked_primrec`: The packed evaluator is primitive recursive.
* `evalnPacked_regComputable`: A register machine computes it.
* `evalnPacked_eq_zero_iff`: It vanishes exactly when the bound is too small.
* `evalnPacked_dom_iff`: Some bound succeeds exactly when the code halts.
-/

namespace LeanBF

namespace Register

open Nat.Partrec

/-- The step-bounded evaluator, taking its bound, code number and input
    packed into one number and returning the encoded `Option`. -/
def evalnPacked (m : Nat) : Nat :=
  Encodable.encode (Code.evaln m.unpair.1
    (Denumerable.ofNat Code m.unpair.2.unpair.1) m.unpair.2.unpair.2)

theorem evalnPacked_primrec : Nat.Primrec evalnPacked := by
  rw [← Primrec.nat_iff]
  unfold evalnPacked
  have harg : Primrec (fun m : Nat => ((m.unpair.1, Denumerable.ofNat Code m.unpair.2.unpair.1),
      m.unpair.2.unpair.2)) := by
    refine Primrec.pair (Primrec.pair ?_ ?_) ?_
    · exact Primrec.fst.comp Primrec.unpair
    · exact (Primrec.ofNat Code).comp (Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair)))
    · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact (Primrec.encode (α := Option Nat)).comp (Code.primrec_evaln.comp harg)

theorem evalnPacked_regComputable : RegComputable evalnPacked :=
  primrec_regComputable evalnPacked_primrec

/-- The encoded result is zero exactly when the bound was too small, which is
    the test the search performs at each candidate. -/
theorem evalnPacked_eq_zero_iff (k c n : Nat) :
    evalnPacked (Nat.pair k (Nat.pair c n)) = 0 ↔
      Code.evaln k (Denumerable.ofNat Code c) n = Option.none := by
  simp only [evalnPacked, Nat.unpair_pair]
  cases h : Code.evaln k (Denumerable.ofNat Code c) n with
  | none => simp only [Encodable.encode_none]
  | some x => simp only [Encodable.encode_some, reduceCtorEq]

/-- A nonzero result carries the answer, one above it. -/
theorem evalnPacked_eq_succ_iff (k c n x : Nat) :
    evalnPacked (Nat.pair k (Nat.pair c n)) = x + 1 ↔
      Code.evaln k (Denumerable.ofNat Code c) n = Option.some x := by
  simp only [evalnPacked, Nat.unpair_pair]
  cases h : Code.evaln k (Denumerable.ofNat Code c) n with
  | none => simp only [Encodable.encode_none, reduceCtorEq]
  | some y =>
      simp only [Encodable.encode_some, Encodable.encode_nat, Option.some.injEq]
      omega

/-- Some bound succeeds exactly when the code halts on the input. This is
    `dom_iff_exists_evaln` restated against the packed evaluator, and is what
    the search's correctness will be measured against. -/
theorem evalnPacked_dom_iff (c n : Nat) :
    (Code.eval (Denumerable.ofNat Code c) n).Dom ↔
      ∃ k, evalnPacked (Nat.pair k (Nat.pair c n)) ≠ 0 := by
  rw [dom_iff_exists_evaln]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun hz => ?_⟩
    rw [(evalnPacked_eq_zero_iff k c n).mp hz] at hk
    exact Bool.noConfusion hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    cases h : Code.evaln k (Denumerable.ofNat Code c) n with
    | none => exact absurd ((evalnPacked_eq_zero_iff k c n).mpr h) hk
    | some x => simp only [Option.isSome_some]

end Register

end LeanBF
