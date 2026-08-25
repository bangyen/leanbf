/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing.Support

/-!
# Register Packing Tests

Kernel re-assertions that a register file packs into one number faithfully,
and that the number a machine starts on is concrete.
-/

namespace LeanBF.Tests

open LeanBF LeanBF.Register

/-- The first two registers use the first two primes, so the packed value of
    a small file can be read off by hand. -/
example : regPrime 0 = 2 := regPrime_zero

example : regPrime 1 = 3 := regPrime_one

/-- A file holding one number in register zero packs to a power of two. This
    is the map a reduction has to name, and nothing about prime enumeration
    survives into it. -/
example (m : Nat) : packRange (fun i => if i = 0 then m else 0) 4 = 2 ^ m :=
  packRange_init m 4 (by omega)

/-- An empty file packs to one. -/
example : packRange (fun _ => 0) 5 = 1 := by
  simpa only [pow_zero] using packRange_init 0 5 (by omega)

/-- Every register below the bound reads back exactly, the other factors
    contributing nothing. -/
example (regs : Nat → Nat) (r : Nat) (hr : r < 6) :
    unpack regPrime (packRange regs 6) r = regs r :=
  unpack_packRange regs 6 r hr

/-- The packed value is never zero, which is what every Gödel lemma needs. -/
example (regs : Nat → Nat) : 0 < packRange regs 9 := packRange_pos regs 9

/-- Incrementing a register multiplies the packed value by its prime. -/
example (regs : Nat → Nat) (v : Nat) :
    packRange (fun i => if i = 2 then v + 1 else regs i) 5
      = regPrime 2 * packRange (fun i => if i = 2 then v else regs i) 5 :=
  packRange_setReg_succ regs 5 2 (by omega) v

/-- A program mentioning no register at all is bounded by zero. -/
example : MentionsBelow [] 0 := by
  intro i hi
  exact absurd hi (by simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true])

/-- And every program has some bound, which is what lets an existentially
    bound machine be packed at all. -/
example (p : Program) : ∃ R, MentionsBelow p R := exists_mentionsBelow p

end LeanBF.Tests
