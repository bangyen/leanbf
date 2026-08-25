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

The theorems below are those three facts. On their own they do not drive a
machine: a register machine cannot multiply or divide directly, so each has
to be realized as a loop over a second counter. `Theory.Packing` does that,
and `Theory.Packing.Simulate` is where these three become the three cases of
one instruction step.

## Main definitions

* `unpack`: A register's value, read out of a packed natural number.
* `regPrime`: The canonical assignment of primes to registers.

## Theorems

* `padicValNat_mul_self`: Multiplying by `p` raises the exponent by one.
* `padicValNat_div_self`: Dividing by `p` lowers the exponent by one.
* `padicValNat_eq_zero_iff_not_dvd`: The exponent is zero exactly when `p`
  does not divide the value.
* `unpack_mul_other`: Incrementing one register leaves the others alone.
* `unpack_div_other`: Decrementing one register leaves the others alone.
* `pack_mul_pos`: A packed value stays positive when a register is
  incremented.
* `pack_div_pos`: A packed value stays positive when a register is
  decremented.
* `regPrime_zero`: The first register's prime is two.
* `regPrime_one`: The second register's prime is three.
* `regPrime_prime`: Every register's prime is prime.
* `regPrime_inj`: Distinct registers get distinct primes.
* `unpack_mul_inc`: Multiplying by a register's prime increments it.
* `unpack_div_dec`: Dividing by a register's prime decrements it.
* `unpack_eq_zero_iff`: A register is zero exactly when its prime does not
  divide the packed value.
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

/-- Register `r`'s value, read out of a packed natural number. -/
def unpack (pr : Nat → Nat) (v r : Nat) : Nat := padicValNat (pr r) v

/-- Multiplying by one prime leaves the other registers alone. -/
theorem unpack_mul_other (p q v : Nat) [Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hv : v ≠ 0) : padicValNat q (p * v) = padicValNat q v := by
  rw [padicValNat.mul (Fact.out (p := p.Prime)).ne_zero hv]
  rw [padicValNat.eq_zero_of_not_dvd]
  · omega
  · intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out (Fact.out (p := p.Prime))).mp hd).symm

/-- Dividing by one prime leaves the other registers alone. -/
theorem unpack_div_other (p q v : Nat) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpq : p ≠ q) (hv : v ≠ 0) (hd : p ∣ v) :
    padicValNat q (v / p) = padicValNat q v := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by
    rintro rfl
    exact hv (Nat.mul_zero p)
  rw [Nat.mul_div_cancel_left k hp.out.pos]
  rw [padicValNat.mul hp.out.ne_zero hk]
  have hnd : ¬ (q ∣ p) := by
    intro hdd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hdd).symm
  rw [padicValNat.eq_zero_of_not_dvd hnd, Nat.zero_add]

/-- A packed value stays positive when multiplied by a prime. -/
theorem pack_mul_pos (p v : Nat) [hp : Fact p.Prime] (hv : 0 < v) : 0 < p * v :=
  Nat.mul_pos hp.out.pos hv

/-- A packed value stays positive when divided by a prime that divides it. -/
theorem pack_div_pos (p v : Nat) [hp : Fact p.Prime] (hv : 0 < v) (hd : p ∣ v) :
    0 < v / p :=
  Nat.div_pos (Nat.le_of_dvd hv hd) hp.out.pos

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

/-- Multiplying the packed value by `pr r` increments register `r` of the
    decoded file and leaves every other register alone. -/
theorem unpack_mul_inc (pr : Nat → Nat) (r : Nat) (v : Nat) (hv : 0 < v)
    (hprime : ∀ n, (pr n).Prime) (hinj : ∀ m n, pr m = pr n → m = n) :
    ∀ r', unpack pr (pr r * v) r' = (if r' = r then unpack pr v r' + 1 else unpack pr v r') := by
  intro r'
  haveI : Fact (pr r).Prime := ⟨hprime r⟩
  haveI : Fact (pr r').Prime := ⟨hprime r'⟩
  by_cases h : r' = r
  · subst h
    rw [if_pos rfl]
    exact padicValNat_mul_self (pr r') v (by omega)
  · rw [if_neg h]
    exact unpack_mul_other (pr r) (pr r') v (fun hc => h (hinj r' r hc.symm)) (by omega)

/-- Dividing the packed value by `pr r` decrements register `r` and leaves
    every other register alone. The divisibility hypothesis is exactly the
    statement that register `r` is non-zero. -/
theorem unpack_div_dec (pr : Nat → Nat) (r : Nat) (v : Nat) (hv : 0 < v)
    (hprime : ∀ n, (pr n).Prime) (hinj : ∀ m n, pr m = pr n → m = n)
    (hdvd : pr r ∣ v) :
    ∀ r', unpack pr (v / pr r) r' = (if r' = r then unpack pr v r' - 1 else unpack pr v r') := by
  intro r'
  haveI : Fact (pr r).Prime := ⟨hprime r⟩
  haveI : Fact (pr r').Prime := ⟨hprime r'⟩
  by_cases h : r' = r
  · subst h
    rw [if_pos rfl]
    exact padicValNat_div_self (pr r') v (by omega) hdvd
  · rw [if_neg h]
    exact unpack_div_other (pr r) (pr r') v (fun hc => h (hinj r' r hc.symm)) (by omega) hdvd

/-- Register `r` is zero exactly when its prime does not divide the packed
    value, so the divisibility test the division loop performs is the
    machine's zero test on the decoded register. -/
theorem unpack_eq_zero_iff (pr : Nat → Nat) (r v : Nat) (hv : 0 < v)
    (hprime : ∀ n, (pr n).Prime) : unpack pr v r = 0 ↔ ¬ (pr r ∣ v) := by
  haveI : Fact (pr r).Prime := ⟨hprime r⟩
  exact padicValNat_eq_zero_iff_not_dvd (pr r) v (by omega)

end LeanBF
