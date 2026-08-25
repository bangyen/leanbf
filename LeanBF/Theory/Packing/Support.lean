/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Godel

/-!
# Finite Support for Register Files

What has to be true of a register machine before its file can be packed into
a single number.

`Theory.Godel` encodes a register file as a product of prime powers, but a
`State`'s registers are a total function `Nat → Nat`, and there is no
finite product over all of them. The encoding therefore has to be taken over
a bounded range, and the registers above that range have to be known to be
zero.

`MentionsBelow` is the syntactic condition that supplies the bound: a program
only ever names finitely many registers, so for any program there is one
below which all of them sit, and `exists_mentionsBelow` produces it — which
is what lets a machine that only exists inside an existential be packed at
all.

Nothing has to be carried about the registers above the bound. An earlier
version tracked that they stay zero, on the theory that the simulation would
otherwise forget them; it does not, because `packRange` only ever reads below
the bound and the simulation relation is stated in terms of `packRange`. The
registers above it are not preserved by the packing — they are simply outside
what it claims.

The bound is a parameter rather than computed from the program. Both are
possible, but the packing layer is stated for every valid bound, so a caller
that knows a convenient one — a fragment's scratch ceiling, say — can use it
instead of the least.

## Main definitions

* `instrMentionsBelow`: One instruction names only registers below a bound.
* `MentionsBelow`: A program names only registers below a bound.
* `packRange`: The packed value of a register file's bounded range.

## Theorems

* `mentionsBelow_of_mem`: The naming condition, stated over membership.
* `exists_mentionsBelow`: Every program has such a bound.
* `packRange_pos`: A packed register file is positive.
* `unpack_packRange`: Reading a register back out of the packed value.
* `packRange_setReg_succ`: Incrementing a register multiplies by its prime.
* `packRange_setReg_pred`: A non-empty register factors its prime out.
* `packRange_init`: One number in register zero packs to a power of two.
-/

namespace LeanBF

namespace Register

/-- The register an instruction touches, if any, lies below the bound. -/
def instrMentionsBelow (R : Nat) : Instruction → Prop
  | .inc r _ => r < R
  | .jzdec r _ _ => r < R
  | .halt => True

/-- Every instruction of the program names only registers below the bound. -/
def MentionsBelow (p : Program) (R : Nat) : Prop :=
  ∀ i (h : i < p.length), instrMentionsBelow R p[i]

/-- The same condition stated over membership rather than indices. Programs
    assembled by appending and flattening are easier to talk about this way,
    every such combinator having a membership lemma. -/
theorem mentionsBelow_of_mem (p : Program) (R : Nat)
    (h : ∀ i ∈ p, instrMentionsBelow R i) : MentionsBelow p R :=
  fun i hi => h p[i] (List.getElem_mem hi)

/-- The packed value of a register file's bounded range: a product of prime
    powers, one factor per register. -/
noncomputable def packRange (regs : Nat → Nat) (R : Nat) : Nat :=
  (Finset.range R).prod (fun r => regPrime r ^ regs r)

/-- A packed register file is positive, being a product of prime powers.
    Every Gödel lemma demands this, and it is why nothing has to carry a
    separate nonzero hypothesis. -/
theorem packRange_pos (regs : Nat → Nat) (R : Nat) : 0 < packRange regs R := by
  refine Finset.prod_pos (fun r _ => ?_)
  exact Nat.pow_pos (regPrime_prime r).pos

/-- Reading a register back out of the packed value. -/
theorem unpack_packRange (regs : Nat → Nat) (R r : Nat) (hr : r < R) :
    unpack regPrime (packRange regs R) r = regs r := by
  classical
  have hp : Fact (regPrime r).Prime := ⟨regPrime_prime r⟩
  -- Split the product into register `r`'s factor and the rest.
  have hsplit : packRange regs R
      = regPrime r ^ regs r * ((Finset.range R).erase r).prod
        (fun q => regPrime q ^ regs q) := by
    rw [packRange, ← Finset.prod_erase_mul _ _ (Finset.mem_range.mpr hr), Nat.mul_comm]
  have hpow : (0 : Nat) < regPrime r ^ regs r := Nat.pow_pos (regPrime_prime r).pos
  have hrestpos : (0 : Nat) < ((Finset.range R).erase r).prod
      (fun q => regPrime q ^ regs q) :=
    Finset.prod_pos (fun q _ => Nat.pow_pos (regPrime_prime q).pos)
  rw [unpack, hsplit, padicValNat.mul (by omega) (by omega),
    padicValNat.prime_pow]
  -- No other register contributes: their primes are all different.
  have hrest : padicValNat (regPrime r) (((Finset.range R).erase r).prod
      (fun q => regPrime q ^ regs q)) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd (fun hdvd => ?_)
    rcases (Prime.dvd_finset_prod_iff (Nat.Prime.prime (regPrime_prime r)) _).mp hdvd with
      ⟨q, hq, hqd⟩
    have hqr : q ≠ r := (Finset.mem_erase.mp hq).1
    -- Dividing a power of another prime forces the two primes equal.
    have := (Nat.Prime.dvd_of_dvd_pow (regPrime_prime r) hqd)
    exact hqr (regPrime_inj q r ((Nat.prime_dvd_prime_iff_eq
      (regPrime_prime r) (regPrime_prime q)).mp this).symm)
  rw [hrest, Nat.add_zero]

/-- Incrementing a register multiplies the packed value by its prime. This
    is a fact about the product, not about prime valuations: `setReg` changes
    exactly one factor, so splitting the product at that register settles
    it. -/
theorem packRange_setReg_succ (regs : Nat → Nat) (R r : Nat) (hr : r < R) (v : Nat) :
    packRange (fun i => if i = r then v + 1 else regs i) R
      = regPrime r * packRange (fun i => if i = r then v else regs i) R := by
  classical
  have hmem : r ∈ Finset.range R := Finset.mem_range.mpr hr
  rw [packRange, packRange, ← Finset.prod_erase_mul _ _ hmem,
    ← Finset.prod_erase_mul _ _ hmem]
  -- The other factors are untouched, the update naming only `r`.
  have hrest : ((Finset.range R).erase r).prod
      (fun q => regPrime q ^ (if q = r then v + 1 else regs q))
      = ((Finset.range R).erase r).prod
        (fun q => regPrime q ^ (if q = r then v else regs q)) := by
    refine Finset.prod_congr rfl (fun q hq => ?_)
    rw [if_neg (Finset.mem_erase.mp hq).1, if_neg (Finset.mem_erase.mp hq).1]
  rw [hrest, if_pos rfl, if_pos rfl, pow_succ]
  ring

/-- The same, read the other way: a register holding a successor factors its
    prime out of the packed value. -/
theorem packRange_setReg_pred (regs : Nat → Nat) (R r : Nat) (hr : r < R)
    (hpos : 0 < regs r) :
    packRange regs R = regPrime r * packRange (fun i => if i = r then regs r - 1 else regs i) R
      := by
  have hkey := packRange_setReg_succ regs R r hr (regs r - 1)
  -- Both sides name the same register file, the update being the identity.
  have hleft : (fun i => if i = r then (regs r - 1) + 1 else regs i) = regs := by
    funext i
    by_cases hi : i = r
    · rw [if_pos hi, hi]
      omega
    · rw [if_neg hi]
  rw [hleft] at hkey
  exact hkey

/-- A register file holding one number in register zero packs to a power of
    two. This is the map a reduction has to exhibit, and it is concrete: no
    prime enumeration survives into it, `regPrime 0` being two. -/
theorem packRange_init (m R : Nat) (hR : 0 < R) :
    packRange (fun i => if i = 0 then m else 0) R = 2 ^ m := by
  classical
  have hmem : (0 : Nat) ∈ Finset.range R := Finset.mem_range.mpr hR
  rw [packRange, ← Finset.prod_erase_mul _ _ hmem, if_pos rfl, regPrime_zero]
  -- Every other register is empty, so contributes a factor of one.
  have hrest : ((Finset.range R).erase 0).prod
      (fun q => regPrime q ^ (if q = 0 then m else 0)) = 1 := by
    refine Finset.prod_eq_one (fun q hq => ?_)
    rw [if_neg (Finset.mem_erase.mp hq).1, pow_zero]
  rw [hrest, Nat.one_mul]

/-- Every program names only finitely many registers, so some bound holds.
    The universal machine is produced by an existential, so its bound cannot
    be written down in advance and has to be extracted from the program
    itself. -/
theorem exists_mentionsBelow (p : Program) : ∃ R, MentionsBelow p R := by
  induction p with
  | nil => exact ⟨0, fun i hi => absurd hi (by simp only [List.length_nil,
      Nat.not_lt_zero, not_false_eq_true])⟩
  | cons a t ih =>
      rcases ih with ⟨R, hR⟩
      -- A bound past both the head's register and the tail's.
      refine ⟨max R (match a with
        | .inc r _ => r + 1
        | .jzdec r _ _ => r + 1
        | .halt => 0), fun i hi => ?_⟩
      rcases i with _ | j
      · -- The head.
        cases a with
        | inc r next => simp only [List.getElem_cons_zero, instrMentionsBelow]; omega
        | jzdec r z nz => simp only [List.getElem_cons_zero, instrMentionsBelow]; omega
        | halt => simp only [List.getElem_cons_zero, instrMentionsBelow]
      · -- The tail, whose bound only grew.
        have hj : j < t.length := by
          simp only [List.length_cons] at hi
          omega
        have := hR j hj
        simp only [List.getElem_cons_succ]
        cases hc : t[j] with
        | inc r next =>
            rw [hc] at this
            simp only [instrMentionsBelow] at this ⊢
            omega
        | jzdec r z nz =>
            rw [hc] at this
            simp only [instrMentionsBelow] at this ⊢
            omega
        | halt => simp only [instrMentionsBelow]

end Register

end LeanBF
