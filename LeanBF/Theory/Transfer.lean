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

`div_reaches` runs the other way, consuming `k` units of the source per unit
added to the target, so the fragment divides by a constant. Division is not
total, and the loop resolves that by encoding the remainder in *where* it
stops: the exit address is `exitBase + n % k`. One fragment therefore answers
both questions the Gödel decrement needs — the quotient, and whether the
prime divided the packed value at all.

`kdrain_reaches` scales the drain: each unit drained adds `k` to the target,
so that fragment multiplies by a constant.

`iterate_reaches` runs an arbitrary body once per unit of a counter register.
The body is a parameter — a state transformer with the fact that it reaches
its result and returns to the loop head — so the lemma applies to any
fragment, not a fixed one. This is what lifts the constant-multiplier loops
to variable arithmetic: multiplying two registers is adding one of them a
number of times given by the other, and primitive recursion is the same shape
with a different body.

`copy_reaches` sends each drained unit to two targets at once. Draining is
destructive, so this is how a register is read without being lost: copy it
into a spare and a scratch, then drain the scratch back. It is the primitive
the pairing arithmetic is built from, since Cantor pairing needs its
arguments more than once. That is what the Gödel encoding needs,
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
* `consumed`: A mid-chain state of the division loop.
* `bumpedAt`: A register raised by one, at a given pointer.
* `divided`: The state after the division loop has run to completion.
* `copied`: The state after the copy loop has run to completion.
* `copyDec`: The copy loop's state after its `jzdec` step.
* `copyMid`: The copy loop's state after its first increment.
* `copyLoop`: The copy loop's state back at the loop head.

## Theorems

* `reaches_trans`: Reachability is transitive.
* `bumped_regs_self`: The bumped register holds its raised value.
* `bumped_regs_other`: Other registers are untouched by a bump.
* `drain_reaches`: The drain loop empties one register into another.
* `inc_chain`: Walking the increment chain raises the target by its length.
* `kdrain_reaches`: The scaled transfer moves `k` units per unit drained.
* `consumed_regs_self`: The consumed register holds its remaining value.
* `consumed_regs_other`: Other registers are untouched mid-chain.
* `chain_short`: The source runs out mid-group, selecting a remainder exit.
* `chain_full`: The source survives a whole group.
* `div_reaches`: The division loop divides by `k`, branching on the
  remainder.
* `copy_reaches`: The copy loop duplicates a register into two others.
* `iterate_reaches`: A counted loop runs a body once per unit of a counter.
* `copyBack_reaches`: A register is copied without being destroyed.
* `copyBack_effect`: The copy stated by its effect on each register.
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

/-- Mid-chain state: pointer at slot `j`, source holding `m`. -/
def consumed (a base j m : Nat) (s : State) : State :=
  { pc := base + j, regs := fun i => if i = a then m else s.regs i }

theorem consumed_regs_self (a base j m : Nat) (s : State) :
    (consumed a base j m s).regs a = m := by
  simp only [consumed, if_true]

theorem consumed_regs_other (a base j m i : Nat) (s : State) (h : i ≠ a) :
    (consumed a base j m s).regs i = s.regs i := by
  simp only [consumed, if_neg h]

/-- The source runs out mid-chain: it exits at `exitBase + (j + m)` with the
    source emptied. -/
theorem chain_short (p : Program) (a base exitBase k : Nat)
    (hchain : ∀ j, j < k → p[base + j]? =
      some (Instruction.jzdec a (exitBase + j) (base + j + 1))) :
    ∀ (m j : Nat), j + m < k → ∀ (s : State), s.pc = base + j → s.regs a = m →
      Reaches p s (consumed a exitBase (j + m) 0 s) := by
  intro m
  induction m with
  | zero =>
      intro j hjk s hpc ha
      have hstep : step p s = some { s with pc := exitBase + j } := by
        simp only [step, hpc, hchain j (by omega), ha, if_pos]
      have hst : ({ pc := exitBase + j, regs := s.regs } : State)
          = consumed a exitBase (j + 0) 0 s := by
        unfold consumed
        ext i
        · simp only
          omega
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, hia, ha]
          · rw [if_neg hia]
      rw [← hst]
      exact Reaches.step s _ _ hstep (Reaches.refl _)
  | succ q ih =>
      intro j hjk s hpc ha
      have hstep : step p s = some (consumed a base (j + 1) q s) := by
        unfold consumed
        simp only [step, hpc, hchain j (by omega), ha, setReg]
        rw [if_neg (by omega)]
        congr 1
      have hpc2 : (consumed a base (j + 1) q s).pc = base + (j + 1) := by
        simp only [consumed]
      have hrec := ih (j + 1) (by omega) (consumed a base (j + 1) q s) hpc2
        (consumed_regs_self a base (j + 1) q s)
      have hfin : consumed a exitBase (j + 1 + q) 0 (consumed a base (j + 1) q s)
          = consumed a exitBase (j + (q + 1)) 0 s := by
        unfold consumed
        ext i
        · simp only
          omega
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
          · rw [if_neg hia, if_neg hia, if_neg hia]
      rw [← hfin]
      exact Reaches.step s _ _ hstep hrec

/-- The source survives the whole group: the chain completes at `base + k`
    having consumed `k - j` units. -/
theorem chain_full (p : Program) (a base exitBase k : Nat)
    (hchain : ∀ j, j < k → p[base + j]? =
      some (Instruction.jzdec a (exitBase + j) (base + j + 1))) :
    ∀ (d j m : Nat), j + d = k → d ≤ m → ∀ (s : State), s.pc = base + j → s.regs a = m →
      Reaches p s (consumed a base k (m - d) s) := by
  intro d
  induction d with
  | zero =>
      intro j m hjk _ s hpc ha
      have hst : s = consumed a base k (m - 0) s := by
        unfold consumed
        ext i
        · simp only [hpc]
          omega
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, hia, ha, Nat.sub_zero]
          · rw [if_neg hia]
      rw [← hst]
      exact Reaches.refl _
  | succ e ih =>
      intro j m hjk hle s hpc ha
      have hm : 0 < m := by omega
      have hstep : step p s = some (consumed a base (j + 1) (m - 1) s) := by
        unfold consumed
        simp only [step, hpc, hchain j (by omega), ha, setReg]
        rw [if_neg (by omega)]
        congr 1
      have hpc2 : (consumed a base (j + 1) (m - 1) s).pc = base + (j + 1) := by
        simp only [consumed]
      have hrec := ih (j + 1) (m - 1) (by omega) (by omega) (consumed a base (j + 1) (m - 1) s)
        hpc2 (consumed_regs_self a base (j + 1) (m - 1) s)
      have hfin : consumed a base k (m - 1 - e) (consumed a base (j + 1) (m - 1) s)
          = consumed a base k (m - (e + 1)) s := by
        unfold consumed
        ext i
        · simp only
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
            omega
          · rw [if_neg hia, if_neg hia, if_neg hia]
      rw [← hfin]
      exact Reaches.step s _ _ hstep hrec

/-- Raise register `t` by one, leaving the pointer at `pc`. -/
def bumpedAt (t pc : Nat) (s : State) : State :=
  { pc := pc, regs := fun i => if i = t then s.regs t + 1 else s.regs i }

/-- The state after dividing: source emptied, target raised by the quotient,
    pointer at the exit encoding the remainder. -/
def divided (a t exitBase q r : Nat) (s : State) : State :=
  { pc := exitBase + r,
    regs := fun i => if i = a then 0 else if i = t then s.regs t + q else s.regs i }

/-- The divide loop: `q` groups of `k` are consumed, each raising the target
    once, and the leftover `r` selects the exit. -/
theorem div_reaches (p : Program) (a t base exitBase k : Nat) (hne : a ≠ t)
    (hchain : ∀ j, j < k → p[base + j]? =
      some (Instruction.jzdec a (exitBase + j) (base + j + 1)))
    (hinc : p[base + k]? = some (Instruction.inc t base)) :
    ∀ (q r : Nat), r < k → ∀ (s : State), s.pc = base → s.regs a = k * q + r →
      Reaches p s (divided a t exitBase q r s) := by
  have hta : ¬ (t = a) := fun hc => hne hc.symm
  intro q
  induction q with
  | zero =>
      intro r hrk s hpc ha
      have ha0 : s.regs a = r := by omega
      have hshort := chain_short p a base exitBase k hchain r 0 (by omega) s (by omega) ha0
      have hfin : consumed a exitBase (0 + r) 0 s = divided a t exitBase 0 r s := by
        unfold consumed divided
        ext i
        · simp only
          omega
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
          · rw [if_neg hia, if_neg hia]
            by_cases hit : i = t
            · rw [if_pos hit, hit, Nat.add_zero]
            · rw [if_neg hit]
      rw [← hfin]
      exact hshort
  | succ n ih =>
      intro r hrk s hpc ha
      -- The source has at least k units, so the whole group is consumed.
      have hexp : s.regs a = k * n + r + k := by
        rw [ha]; ring
      have hfull := chain_full p a base exitBase k hchain k 0 (s.regs a) (by omega)
        (by omega) s (by omega) rfl
      -- Then the inc at base + k raises the target and returns to base.
      have hpcK : (consumed a base k (s.regs a - k) s).pc = base + k := by
        simp only [consumed]
      have hstepInc : step p (consumed a base k (s.regs a - k) s)
          = some (bumpedAt t base (consumed a base k (s.regs a - k) s)) := by
        unfold bumpedAt
        simp only [step, hpcK, hinc, setReg]
      have hpcB : (bumpedAt t base (consumed a base k (s.regs a - k) s)).pc = base := by
        simp only [bumpedAt]
      have hregA : (bumpedAt t base (consumed a base k (s.regs a - k) s)).regs a = k * n + r := by
        simp only [bumpedAt, if_neg hne]
        rw [consumed_regs_self, hexp]
        omega
      have hrec := ih r hrk _ hpcB hregA
      have hfin : divided a t exitBase n r
            (bumpedAt t base (consumed a base k (s.regs a - k) s))
          = divided a t exitBase (n + 1) r s := by
        unfold divided bumpedAt
        ext i
        · simp only
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
          · rw [if_neg hia, if_neg hia]
            by_cases hit : i = t
            · subst hit
              simp only [if_true,
                consumed_regs_other a base k (s.regs a - k) i s hta]
              omega
            · simp only [if_neg hit,
                consumed_regs_other a base k (s.regs a - k) i s hia]
      rw [← hfin]
      exact reaches_trans hfull (Reaches.step _ _ _ hstepInc hrec)

/-- The state after copying `n` units from `a` into both `t1` and `t2`. -/
def copied (a t1 t2 exit n : Nat) (s : State) : State :=
  { pc := exit,
    regs := fun i => if i = a then 0 else if i = t1 then s.regs t1 + n
      else if i = t2 then s.regs t2 + n else s.regs i }

/-- After the first increment of one iteration. -/
def copyMid (a t1 base n : Nat) (s : State) : State :=
  { pc := base + 2, regs := fun i => if i = t1 then s.regs t1 + 1
      else if i = a then n else s.regs i }

/-- After both increments of one iteration, back at the loop head. -/
def copyLoop (a t1 t2 base n : Nat) (s : State) : State :=
  { pc := base, regs := fun i => if i = t2 then s.regs t2 + 1
      else if i = t1 then s.regs t1 + 1 else if i = a then n else s.regs i }

/-- After the jzdec of one iteration. -/
def copyDec (a base n : Nat) (s : State) : State :=
  { pc := base + 1, regs := fun i => if i = a then n else s.regs i }

/-- The copy loop duplicates the source into two targets, emptying it. -/
theorem copy_reaches (p : Program) (a t1 t2 base exit : Nat)
    (h1 : a ≠ t1) (h2 : a ≠ t2) (h12 : t1 ≠ t2)
    (h0 : p[base]? = some (Instruction.jzdec a exit (base + 1)))
    (hi1 : p[base + 1]? = some (Instruction.inc t1 (base + 2)))
    (hi2 : p[base + 2]? = some (Instruction.inc t2 base)) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs a = n →
      Reaches p s (copied a t1 t2 exit n s) := by
  have h1' : t1 ≠ a := fun hc => h1 hc.symm
  have h2' : t2 ≠ a := fun hc => h2 hc.symm
  have h12' : t2 ≠ t1 := fun hc => h12 hc.symm
  intro n
  induction n with
  | zero =>
      intro s hpc ha
      have hstep : step p s = some { s with pc := exit } := by
        simp only [step, hpc, h0, ha, if_pos]
      have hst : ({ pc := exit, regs := s.regs } : State) = copied a t1 t2 exit 0 s := by
        unfold copied
        ext i
        · simp only
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, hia, ha]
          · rw [if_neg hia]
            by_cases hit1 : i = t1
            · rw [if_pos hit1, hit1, Nat.add_zero]
            · rw [if_neg hit1]
              by_cases hit2 : i = t2
              · rw [if_pos hit2, hit2, Nat.add_zero]
              · rw [if_neg hit2]
      rw [← hst]
      exact Reaches.step s _ _ hstep (Reaches.refl _)
  | succ m ih =>
      intro s hpc ha
      have hs1 : step p s = some (copyDec a base m s) := by
        unfold copyDec
        simp only [step, hpc, h0, ha, setReg]
        rw [if_neg (by omega)]
        congr 1
      have hs2 : step p (copyDec a base m s) = some (copyMid a t1 base m s) := by
        unfold copyDec copyMid
        simp only [step, hi1, setReg, if_neg h1']
      have hs3 : step p (copyMid a t1 base m s) = some (copyLoop a t1 t2 base m s) := by
        unfold copyMid copyLoop
        simp only [step, hi2, setReg, if_neg h12', if_neg h2']
      have hpcL : (copyLoop a t1 t2 base m s).pc = base := by simp only [copyLoop]
      have hregL : (copyLoop a t1 t2 base m s).regs a = m := by
        simp only [copyLoop, if_neg h2, if_neg h1, if_true]
      have hrec := ih (copyLoop a t1 t2 base m s) hpcL hregL
      have hfin : copied a t1 t2 exit m (copyLoop a t1 t2 base m s)
          = copied a t1 t2 exit (m + 1) s := by
        unfold copied copyLoop
        ext i
        · simp only
        · simp only []
          by_cases hia : i = a
          · rw [if_pos hia, if_pos hia]
          · rw [if_neg hia, if_neg hia]
            by_cases hit1 : i = t1
            · subst hit1
              simp only [if_neg h12, if_neg hia, if_true]
              omega
            · rw [if_neg hit1, if_neg hit1]
              by_cases hit2 : i = t2
              · subst hit2
                simp only [if_neg hia, if_true, if_neg hit1]
                omega
              · rw [if_neg hit2, if_neg hit2]
                simp only [if_neg hit2, if_neg hit1, if_neg hia]
      rw [← hfin]
      exact Reaches.step s _ _ hs1 (Reaches.step _ _ _ hs2 (Reaches.step _ _ _ hs3 hrec))

/-- Iterating a body: the counter register drives how many times the body
    runs. The body is given abstractly as a state transformer `F` together
    with the fact that it reaches `F s` from `base + 1`, returning to `base`.
    The counter must not be touched by the body. -/
theorem iterate_reaches (p : Program) (c base exit : Nat) (F : State → State)
    (h0 : p[base]? = some (Instruction.jzdec c exit (base + 1)))
    (hbody : ∀ (s : State), s.pc = base + 1 → Reaches p s (F s))
    (hbodyPc : ∀ (s : State), (F s).pc = base)
    (hbodyC : ∀ (s : State), (F s).regs c = s.regs c) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs c = n →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs c = 0 := by
  intro n
  induction n with
  | zero =>
      intro s hpc hc
      refine ⟨{ s with pc := exit }, ?_, rfl, hc⟩
      exact Reaches.step s _ _ (by simp only [step, hpc, h0, hc, if_pos]) (Reaches.refl _)
  | succ m ih =>
      intro s hpc hc
      -- Decrement the counter and enter the body.
      have hstep : step p s
          = some { pc := base + 1, regs := fun i => if i = c then m else s.regs i } := by
        simp only [step, hpc, h0, hc, setReg]
        rw [if_neg (by omega)]
        congr 1
      set s1 : State := { pc := base + 1, regs := fun i => if i = c then m else s.regs i }
      have hbodyRun := hbody s1 rfl
      have hpc2 : (F s1).pc = base := hbodyPc s1
      have hc2 : (F s1).regs c = m := by
        rw [hbodyC s1]
        simp only [s1, if_true]
      rcases ih (F s1) hpc2 hc2 with ⟨s', hrest, hexit, hzero⟩
      exact ⟨s', Reaches.step s s1 s' hstep (reaches_trans hbodyRun hrest), hexit, hzero⟩

/-- Copying a register without destroying it: duplicate into the target and
    a scratch, then drain the scratch back. Draining is destructive, so this
    is the only way a register is read more than once. -/
theorem copyBack_reaches (p : Program) (a t sc base mid exit : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (h0 : p[base]? = some (Instruction.jzdec a mid (base + 1)))
    (hi1 : p[base + 1]? = some (Instruction.inc t (base + 2)))
    (hi2 : p[base + 2]? = some (Instruction.inc sc base))
    (hd0 : p[mid]? = some (Instruction.jzdec sc exit (mid + 1)))
    (hd1 : p[mid + 1]? = some (Instruction.inc a mid)) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs a = n → s.regs sc = 0 →
      Reaches p s (drained sc a exit n (copied a t sc mid n s)) := by
  have hsca : sc ≠ a := fun hc => hasc hc.symm
  have hsct : sc ≠ t := fun hc => htsc hc.symm
  intro n s hpc ha hsc
  have hcopy := copy_reaches p a t sc base mid hat hasc htsc h0 hi1 hi2 n s hpc ha
  have hpc2 : (copied a t sc mid n s).pc = mid := by simp only [copied]
  have hreg2 : (copied a t sc mid n s).regs sc = n := by
    simp only [copied, if_neg hsca, if_neg hsct, if_true, hsc, Nat.zero_add]
  exact reaches_trans hcopy
    (drain_reaches p sc a mid exit hsca hd0 hd1 n _ hpc2 hreg2)

/-- Copy-back stated by its effect rather than by nested state terms: the
    source keeps its value, the target gains it, the scratch stays clear, and
    nothing else moves. -/
theorem copyBack_effect (p : Program) (a t sc base mid exit : Nat)
    (hat : a ≠ t) (hasc : a ≠ sc) (htsc : t ≠ sc)
    (h0 : p[base]? = some (Instruction.jzdec a mid (base + 1)))
    (hi1 : p[base + 1]? = some (Instruction.inc t (base + 2)))
    (hi2 : p[base + 2]? = some (Instruction.inc sc base))
    (hd0 : p[mid]? = some (Instruction.jzdec sc exit (mid + 1)))
    (hd1 : p[mid + 1]? = some (Instruction.inc a mid)) :
    ∀ (s : State), s.pc = base → s.regs sc = 0 →
      ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs a = s.regs a ∧
        s'.regs t = s.regs t + s.regs a ∧ s'.regs sc = 0 ∧
        (∀ r, r ≠ a → r ≠ t → r ≠ sc → s'.regs r = s.regs r) := by
  have hsca : sc ≠ a := fun hc => hasc hc.symm
  have hsct : sc ≠ t := fun hc => htsc hc.symm
  have hta : t ≠ a := fun hc => hat hc.symm
  intro s hpc hsc
  refine ⟨drained sc a exit (s.regs a) (copied a t sc mid (s.regs a) s), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact copyBack_reaches p a t sc base mid exit hat hasc htsc h0 hi1 hi2 hd0 hd1
      (s.regs a) s hpc rfl hsc
  · simp only [drained]
  · simp only [drained, if_neg hasc, if_true, copied, if_true, Nat.zero_add]
  · simp only [drained, if_neg hta, if_neg hat, if_true, copied, if_true, if_neg htsc]
  · simp only [drained, if_true]
  · intro r hra hrt hrsc
    simp only [drained, copied, if_neg hra, if_neg hrt, if_neg hrsc]

end Register

end LeanBF
