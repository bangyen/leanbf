/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Transfer

/-!
# Packed Register Operations

Assembling the transfer loops into the operations a Gödel-encoded register
file needs. A packed register is incremented by multiplying the packed value
by a prime, and multiplication is itself two loops: drain the value into a
scratch register, then transfer it back several units at a time.

This is the first place the two-counter story appears. Each operation uses
one scratch register and leaves it at zero, so a machine holding the packed
value in one counter and using the other as scratch can run any number of
these in sequence. The `hzero` hypothesis and the matching postcondition are
what let them chain.

## Main definitions

* `multiplied`: The state after multiplying a register by a constant.

## Theorems

* `mul_reaches`: Multiplication composes a drain with a scaled transfer.
-/

namespace LeanBF

namespace Register

/-- The state after multiplying register `a` by `k`, scratch `t` restored. -/
def multiplied (a t exit k n : Nat) (s : State) : State :=
  { pc := exit, regs := fun i => if i = t then 0 else if i = a then k * n else s.regs i }

/-- Multiplication composes a drain with a scaled transfer back. -/
theorem mul_reaches (p : Program) (a t base mid exit k : Nat) (hne : a ≠ t) (hk : 0 < k)
    (hd0 : p[base]? = some (Instruction.jzdec a mid (base + 1)))
    (hd1 : p[base + 1]? = some (Instruction.inc t base))
    (hk0 : p[mid]? = some (Instruction.jzdec t exit (mid + 1)))
    (hkc : ∀ j, j < k → p[mid + 1 + j]? =
      some (Instruction.inc a (if j + 1 = k then mid else mid + 2 + j))) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs a = n → s.regs t = 0 →
      Reaches p s (multiplied a t exit k n s) := by
  have hta : t ≠ a := fun hc => hne hc.symm
  intro n s hpc ha ht
  -- Phase one: drain a into t.
  have hdrain := drain_reaches p a t base mid hne hd0 hd1 n s hpc ha
  -- After draining, t holds n and a is zero.
  have hpc2 : (drained a t mid n s).pc = mid := by simp only [drained]
  have hregT : (drained a t mid n s).regs t = n := by
    simp only [drained, if_neg hta, if_true, ht, Nat.zero_add]
  -- Phase two: transfer t back into a, k units per unit.
  have hscale := kdrain_reaches p t a mid exit k hta hk hk0 hkc n
    (drained a t mid n s) hpc2 hregT
  refine reaches_trans hdrain ?_
  have hfin : scaled t a exit k n (drained a t mid n s) = multiplied a t exit k n s := by
    unfold scaled multiplied drained
    ext i
    · simp only
    · simp only []
      by_cases hit : i = t
      · rw [if_pos hit, if_pos hit]
      · rw [if_neg hit, if_neg hit]
        by_cases hia : i = a
        · rw [if_pos hia, if_pos hia]
          simp only [if_true, Nat.zero_add, if_neg hit]
        · rw [if_neg hia, if_neg hia]
          simp only [if_neg hia, if_neg hit]
  rw [← hfin]
  exact hscale

end Register

end LeanBF
