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

/-- The tail's seven slots, at the addresses the layout claims. -/
example : searchTail 2 3 4 5 7 1 3 = [Instruction.jzdec 4 4 3,
    Instruction.jzdec 5 5 7, Instruction.inc 3 6, Instruction.jzdec 7 1 1,
    Instruction.jzdec 5 9 8, Instruction.inc 2 7, Instruction.halt] := rfl

/-- A failed bound clears up, raises the bound, and returns to the head. -/
example (p : Program) (out k arg res blk head base : Nat)
    (hka : k ≠ arg) (hkb : k ≠ blk) (harb : arg ≠ blk) (hra : res ≠ arg)
    (hemb : EmbeddedAt p base (searchTail out k arg res blk head base))
    (s : State) (hpc : s.pc = base) (hres : s.regs res = 0) (hblk : s.regs blk = 0) :
    ∃ s', Reaches p s s' ∧ s'.pc = head ∧ s'.regs arg = 0 ∧
      s'.regs k = s.regs k + 1 ∧ ∀ q, q ≠ arg → q ≠ k → s'.regs q = s.regs q :=
  searchTail_retry p out k arg res blk head base hka hkb harb hra hemb s hpc hres hblk

/-- A successful bound halts with the answer, the test's own decrement having
    decoded it. -/
example (p : Program) (out k arg res blk head base : Nat)
    (hro : res ≠ out) (hra : res ≠ arg) (hoa : out ≠ arg)
    (hemb : EmbeddedAt p base (searchTail out k arg res blk head base))
    (s : State) (x : Nat) (hpc : s.pc = base) (hres : s.regs res = x + 1)
    (hout : s.regs out = 0) :
    ∃ t, RunsTo p s t ∧ t.pc = base + 6 ∧ t.regs out = x :=
  searchTail_stop p out k arg res blk head base hro hra hoa hemb s x hpc hres hout

/-- A nonzero result carries the answer one above it. -/
example (k c n x : Nat) :
    evalnPacked (Nat.pair k (Nat.pair c n)) = x + 1 ↔
      Nat.Partrec.Code.evaln k (Denumerable.ofNat Nat.Partrec.Code c) n = Option.some x :=
  evalnPacked_eq_succ_iff k c n x

end LeanBF.Tests
