/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Register
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Gödel Encoding of Registers

Packing many registers into one counter. A register file is represented by a
single natural number whose prime factorization holds the register values as
exponents: register `r` holds `padicValNat (p r) n` for a choice of distinct
primes `p`.

This is what reduces a machine with arbitrarily many registers to one with a
fixed small number, and it is the reason two counters suffice. The three
register operations become arithmetic on the packed value:

* incrementing register `r` multiplies by `p r`;
* decrementing it divides by `p r`, which is exact because the register being
  non-zero is exactly the statement that `p r` divides the packed value;
* testing whether it is zero asks whether `p r` divides the packed value.

The theorems below are those three facts. What they do not yet do is drive a
machine: a register machine cannot multiply or divide directly, so each of
these has to be realized as a loop over a second counter, which is the next
layer.

## Theorems

* `padicValNat_mul_self`: Multiplying by `p` raises the exponent by one.
* `padicValNat_div_self`: Dividing by `p` lowers the exponent by one.
* `padicValNat_eq_zero_iff_not_dvd`: The exponent is zero exactly when `p`
  does not divide the value.
-/

namespace LeanBF

/-- Multiplying by `p` raises `p`'s exponent by one: the encoded form of
    incrementing a register. -/
theorem padicValNat_mul_self (p n : Nat) [hp : Fact p.Prime] (hn : n ≠ 0) :
    padicValNat p (p * n) = padicValNat p n + 1 := by
  rw [padicValNat.mul hp.out.ne_zero hn, padicValNat_self, Nat.add_comm]

/-- Dividing by `p` lowers `p`'s exponent by one: the encoded form of
    decrementing a register. The division is exact, since `p` divides the
    value exactly when the register is non-zero. -/
theorem padicValNat_div_self (p n : Nat) [hp : Fact p.Prime] (hn : n ≠ 0)
    (hd : p ∣ n) : padicValNat p (n / p) = padicValNat p n - 1 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [Nat.mul_zero, ne_eq, not_true_eq_false] at hn
  rw [Nat.mul_div_cancel_left k hp.out.pos, padicValNat.mul hp.out.ne_zero hk,
    padicValNat_self, Nat.add_sub_cancel_left]

/-- A register is zero exactly when its prime does not divide the packed
    value: the encoded form of the zero test. -/
theorem padicValNat_eq_zero_iff_not_dvd (p n : Nat) [Fact p.Prime] (hn : n ≠ 0) :
    padicValNat p n = 0 ↔ ¬ (p ∣ n) := by
  constructor
  · intro h hd
    have hpos := one_le_padicValNat_of_dvd hn hd
    omega
  · intro h
    exact padicValNat.eq_zero_of_not_dvd h

end LeanBF
