/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Register
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.PrimeCounting

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

What survives here is the third of those, the zero test, which is the only
one stated about a prime valuation. The other two moved: the packing layer
takes its file over a bounded range as a `Finset` product, and updating one
register is then a fact about that product rather than about a valuation —
`Theory.Packing.Support` proves them as `packRange_setReg_succ` and its twin.
An earlier version proved them here in valuation form, and nothing ever used
it.

A register machine cannot multiply or divide directly in any case, so each
operation has to be realized as a loop over a second counter.
`Theory.Packing` does that, and `Theory.Packing.Simulate` is where the three
become the three cases of one instruction step.

## Main definitions

* `unpack`: A register's value, read out of a packed natural number.
* `regPrime`: The canonical assignment of primes to registers.

## Theorems

* `padicValNat_eq_zero_iff_not_dvd`: The exponent is zero exactly when `p`
  does not divide the value.
* `regPrime_zero`: The first register's prime is two.
* `regPrime_one`: The second register's prime is three.
* `regPrime_prime`: Every register's prime is prime.
* `regPrime_inj`: Distinct registers get distinct primes.
* `unpack_eq_zero_iff`: A register is zero exactly when its prime does not
  divide the packed value.
-/

namespace LeanBF

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

/-- Register `r`'s value, read out of a packed natural number. -/
def unpack (pr : Nat → Nat) (v r : Nat) : Nat := padicValNat (pr r) v

/-- The canonical assignment of primes to registers: register `r` uses the
    `r`-th prime. Noncomputable because `Nat.nth` is, which costs nothing
    here — the encoding is a specification, not something the machine runs. -/
noncomputable def regPrime (r : Nat) : Nat := Nat.nth Nat.Prime r

/-- The first two registers' primes, named. The packing layer's initial
    state holds its whole input in register zero, so the map that builds it
    is `2 ^ n` — a concrete function, which is what a later reduction has to
    exhibit as computable. -/
theorem regPrime_zero : regPrime 0 = 2 := by rw [regPrime, Nat.nth_prime_zero_eq_two]

theorem regPrime_one : regPrime 1 = 3 := by rw [regPrime, Nat.nth_prime_one_eq_three]

/-- Every register's prime is prime. -/
theorem regPrime_prime (r : Nat) : (regPrime r).Prime := Nat.prime_nth_prime r

/-- Distinct registers get distinct primes. -/
theorem regPrime_inj (m n : Nat) (h : regPrime m = regPrime n) : m = n :=
  Nat.nth_injective Nat.infinite_setOf_prime h

/-- Register `r` is zero exactly when its prime does not divide the packed
    value, so the divisibility test the division loop performs is the
    machine's zero test on the decoded register. -/
theorem unpack_eq_zero_iff (pr : Nat → Nat) (r v : Nat) (hv : 0 < v)
    (hprime : ∀ n, (pr n).Prime) : unpack pr v r = 0 ↔ ¬ (pr r ∣ v) := by
  haveI : Fact (pr r).Prime := ⟨hprime r⟩
  exact padicValNat_eq_zero_iff_not_dvd (pr r) v (by omega)

end LeanBF
