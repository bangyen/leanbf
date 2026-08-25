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
zero — otherwise the packed value forgets them and the simulation is not
faithful.

`MentionsBelow` is the syntactic condition that makes this hold for free. A
program only ever names finitely many registers, so for any program there is
a bound below which all of them sit; above it, no instruction can write, and
a register that starts at zero stays there. `step_supportedBelow` is that
argument, and it is the only thing standing between a program and a packed
representation of its state.

The bound is a parameter rather than computed from the program. Both are
possible, but the packing layer is stated for every valid bound, so a caller
that knows a convenient one — a fragment's scratch ceiling, say — can use it
instead of the least.

## Main definitions

* `instrMentionsBelow`: One instruction names only registers below a bound.
* `MentionsBelow`: A program names only registers below a bound.
* `SupportedBelow`: A state's registers vanish above a bound.
* `packRange`: The packed value of a register file's bounded range.

## Theorems

* `step_supportedBelow`: Stepping preserves bounded support.
* `reaches_supportedBelow`: Reachability preserves bounded support.
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

/-- The registers at or above the bound are all zero. -/
def SupportedBelow (s : State) (R : Nat) : Prop :=
  ∀ r, R ≤ r → s.regs r = 0

/-- Stepping preserves bounded support. A program that never names a high
    register cannot write to one, so the zeros above the bound stay put. -/
theorem step_supportedBelow (p : Program) (R : Nat) (hm : MentionsBelow p R)
    (s s' : State) (hstep : step p s = some s') (hs : SupportedBelow s R) :
    SupportedBelow s' R := by
  intro r hr
  -- The instruction at the counter is one the program mentions.
  rcases hget : p[s.pc]? with _ | instr
  · rw [step, hget] at hstep
    exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  have hlt : s.pc < p.length := by
    by_contra hc
    rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hc)] at hget
    exact absurd hget (by simp only [reduceCtorEq, not_false_eq_true])
  have hmi : instrMentionsBelow R instr := by
    have heq : p[s.pc] = instr := by
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hget
      exact hget
    rw [← heq]
    exact hm s.pc hlt
  -- No instruction writes above the bound, so the zero there survives.
  cases instr with
  | inc q next =>
      rw [step, hget] at hstep
      simp only [Option.some.injEq] at hstep
      rw [← hstep]
      simp only [setReg]
      rw [if_neg (by simp only [instrMentionsBelow] at hmi; omega)]
      exact hs r hr
  | jzdec q ifZero ifNonZero =>
      by_cases hq : s.regs q = 0
      · have h : step p s = some { s with pc := ifZero } := by
          simp only [step, hget, hq, if_pos]
        rw [h, Option.some.injEq] at hstep
        rw [← hstep]
        exact hs r hr
      · have h : step p s = some { setReg s q (s.regs q - 1) with pc := ifNonZero } := by
          simp only [step, hget, hq, if_false]
        rw [h, Option.some.injEq] at hstep
        rw [← hstep]
        simp only [setReg]
        rw [if_neg (by simp only [instrMentionsBelow] at hmi; omega)]
        exact hs r hr
  | halt =>
      rw [step, hget] at hstep
      exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-- Reachability preserves bounded support, by induction along the path. -/
theorem reaches_supportedBelow (p : Program) (R : Nat) (hm : MentionsBelow p R)
    (s s' : State) (hr : Reaches p s s') (hs : SupportedBelow s R) :
    SupportedBelow s' R := by
  induction hr with
  | refl _ => exact hs
  | step a b _ hstep _ ih => exact ih (step_supportedBelow p R hm a b hstep hs)

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

end Register

end LeanBF
