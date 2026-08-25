/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Register
import Mathlib.Tactic.Ring

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

`kdrain_reaches` scales this: each unit drained adds `k` to the target, so
the fragment multiplies by a constant. That is what the Gödel encoding needs,
since incrementing a packed register means multiplying the packed value by a
prime. Its proof splits in two, an outer induction draining the source and an
inner one (`inc_chain`) walking the chain of increments that runs per unit.

## Main definitions

* `bumped`: A register raised by a constant.
* `decState`: The state after the loop's `jzdec` step.
* `midState`: The state after the loop's `inc` step.
* `drained`: The state after the loop has run to completion.
* `afterDec`: One outer iteration's state after decrementing the source.
* `scaled`: The state after a scaled transfer has run to completion.

## Theorems

* `reaches_trans`: Reachability is transitive.
* `bumped_regs_self`: The bumped register holds its raised value.
* `bumped_regs_other`: Other registers are untouched by a bump.
* `drain_reaches`: The drain loop empties one register into another.
* `inc_chain`: Walking the increment chain raises the target by its length.
* `kdrain_reaches`: The scaled transfer moves `k` units per unit drained.
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

/-- Raise register `t` by `d`, leaving the pointer at `pc`. -/
def bumped (t d pc : Nat) (s : State) : State :=
  { pc := pc, regs := fun i => if i = t then s.regs t + d else s.regs i }

theorem bumped_regs_self (t d pc : Nat) (s : State) : (bumped t d pc s).regs t = s.regs t + d := by
  simp only [bumped, if_true]

theorem bumped_regs_other (t d pc i : Nat) (s : State) (h : i ≠ t) :
    (bumped t d pc s).regs i = s.regs i := by
  simp only [bumped, if_neg h]

/-- Walking the inc-chain from position `base + 1 + j` adds `k - j` to `t`. -/
theorem inc_chain (p : Program) (t base k : Nat)
    (hchain : ∀ j, j < k → p[base + 1 + j]? =
      some (Instruction.inc t (if j + 1 = k then base else base + 2 + j))) :
    ∀ (d j : Nat), j + d = k → 0 < d → ∀ (s : State), s.pc = base + 1 + j →
      Reaches p s (bumped t d base s) := by
  intro d
  induction d with
  | zero => intro j _ hd; omega
  | succ m ih =>
      intro j hjk _ s hpc
      have hjlt : j < k := by omega
      have hstep : step p s
          = some (bumped t 1 (if j + 1 = k then base else base + 2 + j) s) := by
        simp only [step, hpc, hchain j hjlt, setReg, bumped]
      by_cases hlast : j + 1 = k
      · -- last increment: m = 0, and we land on base
        have hm : m = 0 := by omega
        subst hm
        rw [if_pos hlast] at hstep
        exact Reaches.step s _ _ hstep (Reaches.refl _)
      · -- not last: recurse from j+1 with d = m
        rw [if_neg hlast] at hstep
        have hpc' : (bumped t 1 (base + 2 + j) s).pc = base + 1 + (j + 1) := by
          simp only [bumped]
          omega
        have hrec := ih (j + 1) (by omega) (by omega) _ hpc'
        have hcomb : bumped t m base (bumped t 1 (base + 2 + j) s) = bumped t (m + 1) base s := by
          ext i
          · rfl
          · by_cases hit : i = t
            · rw [hit, bumped_regs_self, bumped_regs_self, bumped_regs_self]
              omega
            · rw [bumped_regs_other _ _ _ _ _ hit, bumped_regs_other _ _ _ _ _ hit,
                bumped_regs_other _ _ _ _ _ hit]
        rw [← hcomb]
        exact Reaches.step s _ _ hstep hrec

/-- The state after transferring `n` units from `a`, `k` at a time, into `t`. -/
def scaled (a t exit k n : Nat) (s : State) : State :=
  { pc := exit, regs := fun i => if i = a then 0 else if i = t then s.regs t + k * n else s.regs i }

/-- One outer iteration: decrement the source, then walk the inc-chain. -/
def afterDec (a base m : Nat) (s : State) : State :=
  { pc := base + 1, regs := fun i => if i = a then m else s.regs i }

theorem kdrain_reaches (p : Program) (a t base exit k : Nat) (hne : a ≠ t) (hk : 0 < k)
    (h0 : p[base]? = some (Instruction.jzdec a exit (base + 1)))
    (hchain : ∀ j, j < k → p[base + 1 + j]? =
      some (Instruction.inc t (if j + 1 = k then base else base + 2 + j))) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs a = n →
      Reaches p s (scaled a t exit k n s) := by
  have hta : ¬ (t = a) := fun hc => hne hc.symm
  intro n
  induction n with
  | zero =>
      intro s hpc ha
      have hstep : step p s = some { s with pc := exit } := by
        simp only [step, hpc, h0, ha, if_pos]
      have hst : ({ pc := exit, regs := s.regs } : State) = scaled a t exit k 0 s := by
        unfold scaled
        ext i
        · rfl
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, hia, ha]
          · rw [if_neg hia]
            by_cases hit : i = t
            · rw [if_pos hit, hit, Nat.mul_zero, Nat.add_zero]
            · rw [if_neg hit]
      rw [← hst]
      exact Reaches.step s _ _ hstep (Reaches.refl _)
  | succ m ih =>
      intro s hpc ha
      have hstep1 : step p s = some (afterDec a base m s) := by
        unfold afterDec
        simp only [step, hpc, h0, ha, setReg]
        rw [if_neg (by omega)]
        congr 1
      have hpcd : (afterDec a base m s).pc = base + 1 + 0 := by
        simp only [afterDec]
      have hchainRun := inc_chain p t base k hchain k 0 (by omega) hk _ hpcd
      have hnext : (bumped t k base (afterDec a base m s)).pc = base := by
        simp only [bumped]
      have hnextReg : (bumped t k base (afterDec a base m s)).regs a = m := by
        rw [bumped_regs_other _ _ _ _ _ hne]
        simp only [afterDec, if_true]
      have hrest := ih _ hnext hnextReg
      have hcomb : scaled a t exit k m (bumped t k base (afterDec a base m s))
          = scaled a t exit k (m + 1) s := by
        unfold scaled
        ext i
        · rfl
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
          · rw [if_neg hia, if_neg hia]
            by_cases hit : i = t
            · rw [if_pos hit, if_pos hit, bumped_regs_self]
              simp only [afterDec, if_neg hta]
              ring_nf
            · rw [if_neg hit, if_neg hit, bumped_regs_other _ _ _ _ _ hit]
              simp only [afterDec, if_neg hia]
      rw [← hcomb]
      exact Reaches.step s _ _ hstep1 (reaches_trans hchainRun hrest)

end Register

end LeanBF
