/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Godel

/-!
# Gödel Encoding Tests

Kernel re-assertions of the encoding on a concrete value, and of the zero
test the machine layer branches on.
-/

namespace LeanBF.Tests

open LeanBF

/-- Two registers holding `3` and `2` pack into `2^3 * 3^2 = 72`. -/
example : padicValNat 2 72 = 3 := by
  have h : (72 : Nat) = 2 ^ 3 * 9 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

example : padicValNat 3 72 = 2 := by
  have h : (72 : Nat) = 3 ^ 2 * 8 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- A register absent from the encoding reads as zero. -/
example : padicValNat 5 72 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by norm_num)

/-- Incrementing the first register doubles the packed value: `144 = 2^4 *
    3^2` holds `4` where `72` held `3`. -/
example : padicValNat 2 144 = 4 := by
  have h : (144 : Nat) = 2 ^ 4 * 9 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- And leaves the other registers alone. -/
example : padicValNat 3 144 = 2 := by
  have h : (144 : Nat) = 3 ^ 2 * 16 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- Decrementing halves it: `36 = 2^2 * 3^2`, the second register unmoved. -/
example : padicValNat 2 36 = 2 := by
  have h : (36 : Nat) = 2 ^ 2 * 9 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

example : padicValNat 3 36 = 2 := by
  have h : (36 : Nat) = 3 ^ 2 * 4 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- The zero test is a divisibility test. This is the one the machine layer
    branches on, and the only operation still stated as a valuation. -/
example (n : Nat) (hn : n ≠ 0) : padicValNat 2 n = 0 ↔ ¬ (2 ∣ n) :=
  padicValNat_eq_zero_iff_not_dvd 2 n hn

example (pr : Nat → Nat) (r v : Nat) (hv : 0 < v) (hp : ∀ n, (pr n).Prime) :
    unpack pr v r = 0 ↔ ¬ (pr r ∣ v) :=
  unpack_eq_zero_iff pr r v hv hp

/-- The decoding reads a register out of the packed value. -/
example : unpack (fun r => if r = 0 then 2 else 3) 72 0 = padicValNat 2 72 := rfl

/-- The canonical assignment starts at the first two primes. -/
example : regPrime 0 = 2 := regPrime_zero

example : regPrime 1 = 3 := regPrime_one

/-- And satisfies what the zero test needs, so that statement is not
    vacuous. -/
example (r : Nat) : (regPrime r).Prime := regPrime_prime r

example (m n : Nat) (h : regPrime m = regPrime n) : m = n := regPrime_inj m n h

end LeanBF.Tests
