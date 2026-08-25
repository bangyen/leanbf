/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing.Compile

/-!
# Simulating a Register Machine on Two Counters

The relation that ties the two machines together, and the step that carries
it forward.

`Simulates` says a two-counter state stands for a register machine state:
its packed counter holds the whole register file, its scratch counter is
empty, and its program counter sits at the block the source counter names.
The counter clause is stated through `layout` at the clamped index, so a
source counter past the end of the program lands at the end of the compiled
one, where both machines are equally out of bounds.

`step_simulates` is the whole point of the layer. One source step becomes a
block's worth of packed steps, and the Gödel translation happens here and
nowhere else: a register is zero exactly when its prime fails to divide the
packed value, so `jzdec` reads its branch off `jzdecBlock`'s two cases, and
an increment multiplies the packed value by that prime.

The step count comes back positive because every block opens with a slot
that executes unconditionally. That is what the backward direction will
consume: a source machine that never halts gives a packed machine that keeps
taking steps, and `no_runsTo_of_steps` turns that into non-halting.

## Main definitions

* `Simulates`: A two-counter state stands for a register machine state.

## Theorems

* `step_simulates`: One source step is a block of packed steps.
-/

namespace LeanBF

namespace Register

/-- A two-counter state stands for a register machine state: the packed
    counter holds the file, the scratch is empty, everything above is
    untouched, and the counter names the right block. -/
def Simulates (p : Program) (R : Nat) (s t : State) : Prop :=
  t.pc = layout p s.pc ∧ t.regs 0 = packRange s.regs R ∧
    t.regs 1 = 0 ∧ ∀ q, 2 ≤ q → t.regs q = 0

/-- One source step becomes a block of packed steps, and the simulation
    survives it.

    The three cases are the three block lemmas. An increment multiplies the
    packed value by the register's prime, which is what raising that
    register's exponent means. A `jzdec` divides by it: the register is
    non-zero exactly when the prime divides the packed value, so the two
    branches of `jzdecBlock` are the two branches of the instruction, and the
    quotient the divide leaves is already the decremented file. -/
theorem step_simulates (p : Program) (R : Nat) (hm : MentionsBelow p R)
    (s s' t : State) (hsim : Simulates p R s t)
    (hstep : step p s = some s') :
    ∃ c t', 1 ≤ c ∧ runFor (compile p) c t = some t' ∧ Simulates p R s' t' := by
  obtain ⟨hpc, hpack, hscr, hhigh⟩ := hsim
  -- The counter is in range, or the source machine would not have stepped.
  rcases hget : p[s.pc]? with _ | instr
  · rw [step, hget] at hstep
    exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])
  have hlt : s.pc < p.length := by
    by_contra hc
    rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hc)] at hget
    exact absurd hget (by simp only [reduceCtorEq, not_false_eq_true])
  have hinstr : p[s.pc] = instr := by
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hget
    exact hget
  have hembB : EmbeddedAt (compile p) (layout p s.pc) (compileInstr p s.pc) :=
    embeddedAt_compile p s.pc hlt
  cases instr with
  | inc r next =>
      -- The register is one the program names, so it is inside the packing.
      have hrR : r < R := by
        have := hm s.pc hlt
        rw [hinstr] at this
        exact this
      have hcomp : compileInstr p s.pc
          = incBlock (regPrime r) (layout p s.pc) (layout p next) := by
        rw [compileInstr, hget]
      rw [hcomp] at hembB
      -- The block multiplies the packed value by the register's prime.
      rcases incBlock_reaches (compile p) (regPrime r) (layout p s.pc) (layout p next)
        (regPrime_prime r).pos hembB t hpc hscr with ⟨c, hc, hrun⟩
      refine ⟨c, _, hc, hrun, ?_, ?_, ?_, ?_⟩
      · -- The source counter moved to the instruction's target.
        have hs'pc : s'.pc = next := by
          rw [step, hget] at hstep
          simp only [Option.some.injEq] at hstep
          rw [← hstep]
        rw [hs'pc]
      · -- The packed value gained one factor of the register's prime.
        have hs' : s'.regs = fun i => if i = r then s.regs r + 1 else s.regs i := by
          rw [step, hget] at hstep
          simp only [Option.some.injEq] at hstep
          rw [← hstep]
          rfl
        have hid : (fun i => if i = r then s.regs r else s.regs i) = s.regs := by
          funext i
          by_cases hi : i = r
          · rw [if_pos hi, hi]
          · rw [if_neg hi]
        simp only [if_pos trivial, hpack, hs']
        rw [packRange_setReg_succ s.regs R r hrR (s.regs r), hid]
      · simp only [if_neg (by omega : ¬ (1 : Nat) = 0), if_pos trivial]
      · intro q hq
        simp only [if_neg (by omega : ¬ q = 0), if_neg (by omega : ¬ q = 1)]
        exact hhigh q hq
  | jzdec r ifZero ifNonZero =>
      have hrR : r < R := by
        have := hm s.pc hlt
        rw [hinstr] at this
        exact this
      have hcomp : compileInstr p s.pc
          = jzdecBlock (regPrime r) (layout p s.pc) (layout p ifZero)
            (layout p ifNonZero) := by
        rw [compileInstr, hget]
      rw [hcomp] at hembB
      -- The register's value is its prime's exponent in the packed value.
      have hpos : 0 < packRange s.regs R := packRange_pos s.regs R
      have hread : unpack regPrime (packRange s.regs R) r = s.regs r :=
        unpack_packRange s.regs R r hrR
      -- Zero exactly when the prime does not divide: the test, translated.
      have hiff : s.regs r = 0 ↔ ¬ (regPrime r ∣ packRange s.regs R) := by
        rw [← hread]
        exact unpack_eq_zero_iff regPrime r _ hpos regPrime_prime
      by_cases hz : s.regs r = 0
      · -- The register was zero: the file comes back untouched.
        have hs'eq : s' = { s with pc := ifZero } := by
          have h : step p s = some { s with pc := ifZero } := by
            simp only [step, hget, hz, if_pos]
          rw [h, Option.some.injEq] at hstep
          exact hstep.symm
        have hndvd : ¬ (regPrime r ∣ t.regs 0) := by
          rw [hpack]
          exact hiff.mp hz
        rcases jzdecBlock_ndvd (compile p) (regPrime r) (layout p s.pc) (layout p ifZero)
          (layout p ifNonZero) (regPrime_prime r).pos hembB t hpc hscr hndvd with
          ⟨c, hc, hrun⟩
        refine ⟨c, _, hc, hrun, ?_, ?_, ?_, ?_⟩
        · rw [hs'eq]
        · -- Nothing changed, so the packed value is what it was.
          simp only [if_pos trivial, hs'eq]
          exact hpack
        · simp only [if_neg (by omega : ¬ (1 : Nat) = 0), if_pos trivial]
        · intro q hq
          simp only [if_neg (by omega : ¬ q = 0), if_neg (by omega : ¬ q = 1)]
          exact hhigh q hq
      · -- The register was non-zero: the divide is the decrement.
        have hs'eq : s' = { setReg s r (s.regs r - 1) with pc := ifNonZero } := by
          have h : step p s = some { setReg s r (s.regs r - 1) with pc := ifNonZero } := by
            simp only [step, hget, hz, if_false]
          rw [h, Option.some.injEq] at hstep
          exact hstep.symm
        have hdvd : regPrime r ∣ t.regs 0 := by
          rw [hpack]
          by_contra hc
          exact hz (hiff.mpr hc)
        rcases jzdecBlock_dvd (compile p) (regPrime r) (layout p s.pc) (layout p ifZero)
          (layout p ifNonZero) (regPrime_prime r).pos hembB t hpc hscr hdvd with
          ⟨c, hc, hrun⟩
        refine ⟨c, _, hc, hrun, ?_, ?_, ?_, ?_⟩
        · rw [hs'eq]
        · -- The quotient is the file with that register lowered by one.
          simp only [if_pos trivial, hpack, hs'eq, setReg]
          -- Dividing out the prime is exactly lowering that exponent.
          rw [packRange_setReg_pred s.regs R r hrR (by omega),
            Nat.mul_div_cancel_left _ (regPrime_prime r).pos]
        · simp only [if_neg (by omega : ¬ (1 : Nat) = 0), if_pos trivial]
        · intro q hq
          simp only [if_neg (by omega : ¬ q = 0), if_neg (by omega : ¬ q = 1)]
          exact hhigh q hq
  | halt =>
      -- A halt does not step, so this case is vacuous.
      rw [step, hget] at hstep
      exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

end Register

end LeanBF
