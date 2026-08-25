/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Godel

/-!
# Gödel Encoding Tests

Kernel re-assertions of the packed register operations, and of the encoding
itself on a concrete value.
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

/-- Incrementing the first register doubles the packed value. -/
example (n : Nat) (hn : n ≠ 0) : padicValNat 2 (2 * n) = padicValNat 2 n + 1 :=
  padicValNat_mul_self 2 n hn

/-- Decrementing halves it, exactly, because the register was non-zero. -/
example (n : Nat) (hn : n ≠ 0) (hd : 2 ∣ n) :
    padicValNat 2 (n / 2) = padicValNat 2 n - 1 :=
  padicValNat_div_self 2 n hn hd

/-- The zero test is a divisibility test. -/
example (n : Nat) (hn : n ≠ 0) : padicValNat 2 n = 0 ↔ ¬ (2 ∣ n) :=
  padicValNat_eq_zero_iff_not_dvd 2 n hn

/-- Concretely: `72` holds `3` in its first register, so `144` holds `4`. -/
example : padicValNat 2 144 = 4 := by
  have h : (144 : Nat) = 2 * 72 := by norm_num
  have h72 : padicValNat 2 72 = 3 := by
    have h9 : (72 : Nat) = 2 ^ 3 * 9 := by norm_num
    rw [h9, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [h, padicValNat_mul_self 2 72 (by norm_num), h72]

/-- Registers are independent: incrementing one leaves the others alone.
    Here `72 = 2^3 * 3^2` becomes `144 = 2^4 * 3^2`. -/
example : padicValNat 3 144 = padicValNat 3 72 := by
  have h : (144 : Nat) = 2 * 72 := by norm_num
  rw [h]
  exact unpack_mul_other 2 3 72 (by norm_num) (by norm_num)

/-- The same holds for a decrement: `72` becomes `36 = 2^2 * 3^2`. -/
example : padicValNat 3 36 = padicValNat 3 72 := by
  have h : (36 : Nat) = 72 / 2 := by norm_num
  rw [h]
  exact unpack_div_other 2 3 72 (by norm_num) (by norm_num) (by norm_num)

/-- A packed file never reaches zero, which the exponent lemmas require. -/
example (v : Nat) (hv : 0 < v) : 0 < 2 * v :=
  pack_mul_pos 2 v hv

example (v : Nat) (hv : 0 < v) (hd : 2 ∣ v) : 0 < v / 2 :=
  pack_div_pos 2 v hv hd

/-- The decoding reads a register out of the packed value. -/
example : unpack (fun r => if r = 0 then 2 else 3) 72 0 = padicValNat 2 72 := rfl

end LeanBF.Tests
