/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Register

/-!
# Register Transfer Loops

The drain loop, which empties one register into another. This is the
fundamental register machine idiom: a counter machine cannot read a register
without destroying it, so every operation is built by draining a register and
rebuilding what it held.

Correctness is stated with `Reaches` rather than `RunsTo`. A fragment sitting
inside a larger program does not halt when it finishes; it hands control to
whatever follows. `Reaches` says only where the machine ends up, which is
what composes, and `reaches_trans` chains fragments together.

The loop occupies two instructions at `base`, and the theorem takes the
program as a parameter with hypotheses pinning those two slots, so a fragment
can be placed anywhere inside a larger program.

## Main definitions

* `decState`: The state after the loop's `jzdec` step.
* `midState`: The state after the loop's `inc` step.
* `drained`: The state after the loop has run to completion.

## Theorems

* `reaches_trans`: Reachability is transitive.
* `drain_reaches`: The drain loop empties one register into another.
-/

namespace LeanBF

namespace Register

theorem reaches_trans {p : Program} {a b c : State}
    (h1 : Reaches p a b) (h2 : Reaches p b c) : Reaches p a c := by
  induction h1 with
  | refl s => exact h2
  | step s s' s'' hstep _ ih => exact Reaches.step s s' c hstep (ih h2)

/-- After the `jzdec` step: pointer advanced, source decremented. -/
def decState (a base k : Nat) (s : State) : State :=
  { pc := base + 1, regs := fun i => if i = a then k else s.regs i }

/-- After the `inc` step: back at the loop head, target raised. -/
def midState (a t base k : Nat) (s : State) : State :=
  { pc := base, regs := fun i => if i = t then s.regs t + 1 else if i = a then k else s.regs i }

/-- The state after draining `n` units from `a` into `t`. -/
def drained (a t exit n : Nat) (s : State) : State :=
  { pc := exit, regs := fun i => if i = a then 0 else if i = t then s.regs t + n else s.regs i }

theorem drain_reaches (p : Program) (a t base exit : Nat) (hne : a ≠ t)
    (h0 : p[base]? = some (Instruction.jzdec a exit (base + 1)))
    (h1 : p[base + 1]? = some (Instruction.inc t base)) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs a = n →
      Reaches p s (drained a t exit n s) := by
  have hta : ¬ (t = a) := fun hc => hne hc.symm
  intro n
  induction n with
  | zero =>
      intro s hpc ha
      have hstep : step p s = some { s with pc := exit } := by
        simp only [step, hpc, h0, ha, if_pos]
      have hst : ({ pc := exit, regs := s.regs } : State) = drained a t exit 0 s := by
        unfold drained
        ext i
        · rfl
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, hia, ha]
          · rw [if_neg hia]
            by_cases hit : i = t
            · rw [if_pos hit, hit, Nat.add_zero]
            · rw [if_neg hit]
      rw [← hst]
      exact Reaches.step s _ _ hstep (Reaches.refl _)
  | succ k ih =>
      intro s hpc ha
      have hstep1 : step p s = some (decState a base k s) := by
        unfold decState
        simp only [step, hpc, h0, ha, Register.setReg]
        rw [if_neg (by omega)]
        congr 1
      have hstep2 : step p (decState a base k s) = some (midState a t base k s) := by
        unfold decState midState
        simp only [step, h1, Register.setReg, if_neg hta]
      have hreg : (midState a t base k s).regs a = k := by
        unfold midState
        simp only [if_neg hne, if_true]
      have hrest := ih (midState a t base k s) rfl hreg
      refine Reaches.step s _ _ hstep1 (Reaches.step _ _ _ hstep2 ?_)
      have hfin : drained a t exit k (midState a t base k s) = drained a t exit (k + 1) s := by
        unfold drained
        ext i
        · rfl
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
          · rw [if_neg hia, if_neg hia]
            by_cases hit : i = t
            · rw [if_pos hit, if_pos hit]
              unfold midState
              simp only [if_true]
              omega
            · rw [if_neg hit, if_neg hit]
              unfold midState
              simp only [if_neg hit, if_neg hia]
      rw [← hfin]
      exact hrest

end Register

end LeanBF
