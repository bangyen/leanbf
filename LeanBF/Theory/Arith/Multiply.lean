/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Transfer

/-!
# Variable Multiplication

Multiplying two registers by repeated addition. `kdrain_reaches` already
scales by a constant, but a constant is compiled into the length of an
increment chain, so it cannot answer a factor that only exists at runtime.
Here both factors are registers.

The shape is a counted loop over one factor whose body adds the other. What
makes it fit `iterate_inv` is that the body must not disturb the counter and
must return to the loop head. Both fall out of `copyBack_effect`: its final
drain takes the exit address as a parameter, so the body is pointed straight
back at the loop head with no unconditional jump to fake, and the counter is
simply a register the body never names.

The invariant is indexed by the iterations *remaining*, so it reads
`t = t₀ + a * (b₀ - m)`. Stating it in terms of the original `b₀` rather than
counting upward is what lets `iterate_inv`'s conclusion at `m = 0` be the
answer directly.

## Main definitions

* `MulInv`: The multiplication loop's invariant on the register file.

## Theorems

* `mulInv_congr`: The invariant ignores the counter register.
* `mul_body_effect`: One iteration adds the multiplicand and returns.
* `mulVar_effect`: Two registers are multiplied into a third.
-/

namespace LeanBF

namespace Register

/-- The multiplication loop's invariant, indexed by iterations remaining:
    the target holds its original value plus as many copies of `a` as have
    already been added. `a` and the original values are parameters, so the
    invariant constrains only the target and the multiplicand. -/
def MulInv (a t sc : Nat) (a0 t0 b0 : Nat) (m : Nat) (f : Nat → Nat) : Prop :=
  m ≤ b0 ∧ f a = a0 ∧ f sc = 0 ∧ f t = t0 + a0 * (b0 - m)

theorem mulInv_congr (a t sc a0 t0 b0 c : Nat) (hac : a ≠ c) (htc : t ≠ c) (hscc : sc ≠ c) :
    ∀ (m : Nat) (f g : Nat → Nat), (∀ i, i ≠ c → f i = g i) →
      MulInv a t sc a0 t0 b0 m f → MulInv a t sc a0 t0 b0 m g := by
  intro m f g hfg hI
  exact ⟨hI.1, by rw [← hfg a hac]; exact hI.2.1, by rw [← hfg sc hscc]; exact hI.2.2.1,
    by rw [← hfg t htc]; exact hI.2.2.2⟩

/-- One iteration of the multiplication loop: add `a` into `t` and come back
    to the loop head with the counter untouched. -/
theorem mul_body_effect (p : Program) (a t sc c base : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (hac : a ≠ c) (htc : t ≠ c) (hscc : sc ≠ c)
    (a0 t0 b0 : Nat)
    (h0 : p[base + 1]? = some (Instruction.jzdec a (base + 4) (base + 2)))
    (hi1 : p[base + 2]? = some (Instruction.inc t (base + 3)))
    (hi2 : p[base + 3]? = some (Instruction.inc sc (base + 1)))
    (hd0 : p[base + 4]? = some (Instruction.jzdec sc base (base + 5)))
    (hd1 : p[base + 5]? = some (Instruction.inc a (base + 4))) :
    ∀ (m : Nat) (s : State), s.pc = base + 1 → s.regs c = m →
      MulInv a t sc a0 t0 b0 (m + 1) s.regs →
      ∃ s', Reaches p s s' ∧ s'.pc = base ∧ s'.regs c = m ∧
        MulInv a t sc a0 t0 b0 m s'.regs := by
  intro m s hpc hc hI
  have hmb : m + 1 ≤ b0 := hI.1
  rcases copyBack_effect p a t sc (base + 1) (base + 4) base hat hasc htsc
    h0 hi1 hi2 hd0 hd1 s hpc hI.2.2.1 with ⟨s', hr, hpc', hA, hT, hS, hF⟩
  refine ⟨s', hr, hpc', ?_, by omega, hA.trans hI.2.1, hS, ?_⟩
  · rw [hF c (fun hcc => hac hcc.symm) (fun hcc => htc hcc.symm) (fun hcc => hscc hcc.symm), hc]
  · -- One more copy of `a` has landed, so the remaining count drops by one.
    -- The counter never exceeds its starting value, so the subtraction is exact.
    rw [hT, hI.2.2.2, hI.2.1]
    have hsplit : b0 - m = (b0 - (m + 1)) + 1 := by omega
    rw [hsplit]
    ring

/-- Multiplying two registers into a third. The counter `b` is consumed;
    `a` survives, since each iteration copies it back. -/
theorem mulVar_effect (p : Program) (a b t sc base exit : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (hab : a ≠ b) (hbt : b ≠ t) (hbsc : b ≠ sc)
    (hloop : p[base]? = some (Instruction.jzdec b exit (base + 1)))
    (h0 : p[base + 1]? = some (Instruction.jzdec a (base + 4) (base + 2)))
    (hi1 : p[base + 2]? = some (Instruction.inc t (base + 3)))
    (hi2 : p[base + 3]? = some (Instruction.inc sc (base + 1)))
    (hd0 : p[base + 4]? = some (Instruction.jzdec sc base (base + 5)))
    (hd1 : p[base + 5]? = some (Instruction.inc a (base + 4))) :
    ∀ (s : State), s.pc = base → s.regs sc = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs b = 0 ∧
        s'.regs a = s.regs a ∧ s'.regs sc = 0 ∧
        s'.regs t = s.regs t + s.regs a * s.regs b := by
  intro s hpc hsc
  rcases iterate_inv p b base exit (MulInv a t sc (s.regs a) (s.regs t) (s.regs b))
    (mulInv_congr a t sc (s.regs a) (s.regs t) (s.regs b) b
      (fun hc => hab hc) (fun hc => hbt hc.symm) (fun hc => hbsc hc.symm))
    hloop
    (fun m s1 hpc1 hc1 hI1 => mul_body_effect p a t sc b base hat hasc htsc
      (fun hc => hab hc) (fun hc => hbt hc.symm) (fun hc => hbsc hc.symm)
      (s.regs a) (s.regs t) (s.regs b) h0 hi1 hi2 hd0 hd1 m s1 hpc1 hc1 hI1)
    (s.regs b) s hpc rfl
    ⟨le_refl _, rfl, hsc, by rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]⟩ with
    ⟨s', hr, hpc', hb', hI'⟩
  refine ⟨s', hr, hpc', hb', hI'.2.1, hI'.2.2.1, ?_⟩
  rw [hI'.2.2.2, Nat.sub_zero]

end Register

end LeanBF
