/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Trace
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
* `searchTail`: The seven slots that test a bound and either retry or stop.

## Theorems

* `evalnPacked_primrec`: The packed evaluator is primitive recursive.
* `evalnPacked_regComputable`: A register machine computes it.
* `evalnPacked_eq_zero_iff`: It vanishes exactly when the bound is too small.
* `evalnPacked_eq_succ_iff`: A nonzero result carries the answer.
* `evalnPacked_dom_iff`: Some bound succeeds exactly when the code halts.
* `searchTail_retry`: A failed bound clears up and raises the bound.
* `searchTail_stop`: A successful bound decodes the answer and halts.
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

/-- The slots after the evaluator's fragment: clear the argument, test the
    result, and either raise the bound and go round again or stop with the
    answer.

    The test is a single `jzdec`. A zero result means the bound was too
    small; a nonzero one is `x + 1`, and the same instruction's decrement
    turns it into `x`, so nothing separate has to decode it. The return to
    the head tests a register the loop keeps empty, the machine having no
    plain jump. -/
def searchTail (out k arg res blk head base : Nat) : Program :=
  [Instruction.jzdec arg (base + 1) base,
   Instruction.jzdec res (base + 2) (base + 4),
   Instruction.inc k (base + 3),
   Instruction.jzdec blk head head,
   Instruction.jzdec res (base + 6) (base + 5),
   Instruction.inc out (base + 4),
   Instruction.halt]

/-- A bound that failed: clear the argument, fall through the test, raise
    the bound, and return to the head. -/
theorem searchTail_retry (p : Program) (out k arg res blk head base : Nat)
    (hka : k ≠ arg) (hkb : k ≠ blk) (harb : arg ≠ blk) (hra : res ≠ arg)
    (hemb : EmbeddedAt p base (searchTail out k arg res blk head base)) :
    ∀ (s : State), s.pc = base → s.regs res = 0 → s.regs blk = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = head ∧ s'.regs arg = 0 ∧
        s'.regs k = s.regs k + 1 ∧ ∀ q, q ≠ arg → q ≠ k → s'.regs q = s.regs q := by
  intro s hpc hres hblk
  have hg := embeddedAt_get p base _ hemb
  -- Clear the argument the evaluator consumed.
  have hclr := clear_reaches p arg base (base + 1)
    (by simpa only [Nat.add_zero] using hg 0 _ rfl) (s.regs arg) s hpc rfl
  set s1 : State := { pc := base + 1, regs := fun i => if i = arg then 0 else s.regs i }
    with hs1
  -- The test falls through, the result being zero.
  have hres1 : s1.regs res = 0 := by
    simp only [hs1, if_neg hra]
    exact hres
  have hstepTest : step p s1 = some { s1 with pc := base + 2 } := by
    rw [step, hs1]
    simp only [hg 1 _ rfl, if_neg hra, hres, if_pos]
  -- Raise the bound.
  have hstepInc : step p { s1 with pc := base + 2 }
      = some { setReg s1 k (s1.regs k + 1) with pc := base + 3 } := by
    simp only [step, hs1, hg 2 _ rfl, setReg]
  set s3 : State := { setReg s1 k (s1.regs k + 1) with pc := base + 3 } with hs3
  -- Return to the head, testing a register the loop keeps empty.
  have hblk3 : s3.regs blk = 0 := by
    simp only [hs3, setReg, if_neg (Ne.symm hkb), hs1, if_neg (Ne.symm harb)]
    exact hblk
  have hjump : step p s3 = some { s3 with pc := head } := by
    rw [step, hs3]
    simp only [hg 3 _ rfl]
    rw [show (setReg s1 k (s1.regs k + 1)).regs blk = 0 from hblk3]
    simp only [if_pos]
  refine ⟨{ s3 with pc := head }, reaches_trans hclr (Reaches.step _ _ _ hstepTest
    (Reaches.step _ _ _ hstepInc (Reaches.step _ _ _ hjump (Reaches.refl _)))), rfl, ?_, ?_, ?_⟩
  · simp only [hs3, setReg, if_neg (Ne.symm hka), hs1, if_pos]
  · simp only [hs3, setReg, if_pos, hs1, if_neg hka]
  · intro q hqa hqk
    simp only [hs3, setReg, if_neg hqk, hs1, if_neg hqa]

/-- A bound that succeeded: the test's own decrement decodes the answer,
    which is then drained to the output, and the machine halts. -/
theorem searchTail_stop (p : Program) (out k arg res blk head base : Nat)
    (hro : res ≠ out) (hra : res ≠ arg) (hoa : out ≠ arg)
    (hemb : EmbeddedAt p base (searchTail out k arg res blk head base)) :
    ∀ (s : State) (x : Nat), s.pc = base → s.regs res = x + 1 → s.regs out = 0 →
      ∃ t, RunsTo p s t ∧ t.pc = base + 6 ∧ t.regs out = x := by
  intro s x hpc hres hout
  have hg := embeddedAt_get p base _ hemb
  -- Clear the argument the evaluator consumed.
  have hclr := clear_reaches p arg base (base + 1)
    (by simpa only [Nat.add_zero] using hg 0 _ rfl) (s.regs arg) s hpc rfl
  set s1 : State := { pc := base + 1, regs := fun i => if i = arg then 0 else s.regs i }
    with hs1
  -- The test finds a nonzero result, and its decrement is the decoding.
  have hres1 : s1.regs res = x + 1 := by
    simp only [hs1, if_neg hra]
    exact hres
  have hstepTest : step p s1 = some { setReg s1 res x with pc := base + 4 } := by
    rw [step, hs1]
    simp only [hg 1 _ rfl, if_neg hra, hres, setReg]
    rw [if_neg (by omega : ¬ (x + 1 = 0)), Nat.add_sub_cancel]
  set s2 : State := { setReg s1 res x with pc := base + 4 } with hs2
  -- Drain the answer into the output.
  have hdrain := drain_reaches p res out (base + 4) (base + 6) hro
    (hg 4 _ rfl) (hg 5 _ rfl) (s2.regs res) s2 rfl rfl
  set s3 : State := drained res out (base + 6) (s2.regs res) s2 with hs3
  refine ⟨s3, ?_, by simp only [hs3, drained], ?_⟩
  · -- The drain lands on the halt slot, which terminates the run.
    refine runsTo_of_reaches_halt p s s3
      (reaches_trans hclr (Reaches.step _ _ _ hstepTest hdrain)) (Or.inl ?_)
    simp only [hs3, drained]
    exact hg 6 _ rfl
  · simp only [hs3, drained, if_neg (Ne.symm hro), if_pos, hs2, setReg, if_pos, hs1,
      if_neg hoa]
    rw [hout, Nat.zero_add]

end Register

end LeanBF
