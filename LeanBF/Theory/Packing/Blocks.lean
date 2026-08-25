/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Embed
import LeanBF.Theory.Packing.Support
import LeanBF.Theory.Trace
import LeanBF.Theory.Transfer

/-!
# The Two-Counter Blocks

What one source instruction becomes once the register file is a single
number.

A register machine cannot multiply or divide, so the arithmetic the Gödel
encoding calls for has to be realized as loops over a second counter. Both
loops already exist in `Theory.Transfer`, built for the fragment layer: the
scaled transfer moves a counter across `k` units at a time, multiplying by
`k`, and the divide loop consumes groups of `k` and *branches on the
remainder by exit address*.

That branching is what makes the conditional free, the same way the search
tail's single `jzdec` both tested and decoded. Dividing the packed value by
register `r`'s prime answers the zero test and performs the decrement at
once: a remainder of zero means the prime divides the packed value, so the
register was non-zero, and the quotient is already the decremented file.

The cost is that a divide is destructive. On a non-zero remainder — the
register was zero, and the file must be handed back untouched — the packed
value is gone, its quotient in the scratch counter and its remainder recorded
only in which exit was taken. Each remainder therefore gets its own restore
block, which multiplies the quotient back up and adds that remainder's worth
of units as literal increments. There are `p - 1` such blocks, which is why
a `jzdec` block's length grows with the register's prime.

## Main definitions

* `incBlock`: The block that increments a packed register.
* `restoreArm`: The arm that rebuilds a packed value the divide destroyed.
* `restored`: The state a restore arm leaves.
* `paddedArm`: A restore arm padded to a uniform length.

## Theorems

* `incBlock_get_entry`: The block's entry no-op.
* `incBlock_get_head`: The block's opening test.
* `incBlock_get_chain`: The block's increment chain.
* `incBlock_get_drain0`: The drain loop's test.
* `incBlock_get_drain1`: The drain loop's increment.
* `incBlockLen`: The increment block's length.
* `incBlock_reaches`: The increment block multiplies by the register's prime.
* `restoreArm_length`: A restore arm's length.
* `paddedArm_length`: A padded arm's uniform length.
* `embeddedAt_paddedArm`: A padded arm embeds the arm inside it.
* `restoreArm_get_head`: The arm's opening test.
* `restoreArm_get_chain`: The arm's multiply-back chain.
* `restoreArm_get_units`: The arm's literal remainder units.
* `restoreArm_units_reaches`: Walking the arm's literal units.
* `restoreArm_reaches`: The arm rebuilds the value the divide destroyed.
-/

namespace LeanBF

namespace Register

/-- The block that increments a packed register: move the packed value into
    the scratch counter `p` units at a time, then pour it back. The scaled
    transfer is the multiplication; the drain only undoes the displacement. -/
def incBlock (p base exit : Nat) : Program :=
  [Instruction.jzdec 1 (base + 1) (base + 1),
   Instruction.jzdec 0 (base + 2 + p) (base + 2)]
  ++ (List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base + 1 else base + 3 + j))
  ++ [Instruction.jzdec 1 exit (base + 2 + p + 1), Instruction.inc 0 (base + 2 + p)]

theorem incBlockLen (p base exit : Nat) : (incBlock p base exit).length = p + 4 := by
  simp only [incBlock, List.length_append, List.length_cons, List.length_map,
    List.length_range, List.length_nil]
  omega

/-- Reading the increment block's slots. The block is three pieces appended,
    so indexing it is a case split on which piece the offset lands in; doing
    that once here keeps it out of the effect proof. -/
theorem incBlock_get_entry (p base exit : Nat) :
    (incBlock p base exit)[0]? =
      some (Instruction.jzdec 1 (base + 1) (base + 1)) := rfl

theorem incBlock_get_head (p base exit : Nat) :
    (incBlock p base exit)[1]? =
      some (Instruction.jzdec 0 (base + 2 + p) (base + 2)) := rfl

theorem incBlock_get_chain (p base exit j : Nat) (hj : j < p) :
    (incBlock p base exit)[2 + j]? =
      some (Instruction.inc 1 (if j + 1 = p then base + 1 else base + 3 + j)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base + 1 else base + 3 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [incBlock, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show 2 + j - 2 = j by omega]
  rw [List.getElem?_append_left (by rw [hlen]; exact hj), List.getElem?_map,
    List.getElem?_range hj]
  rfl

theorem incBlock_get_drain0 (p base exit : Nat) :
    (incBlock p base exit)[p + 2]? =
      some (Instruction.jzdec 1 exit (base + 2 + p + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base + 1 else base + 3 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [incBlock, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show p + 2 - 2 = p by omega]
  rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

theorem incBlock_get_drain1 (p base exit : Nat) :
    (incBlock p base exit)[p + 3]? = some (Instruction.inc 0 (base + 2 + p)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base + 1 else base + 3 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [incBlock, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show p + 3 - 2 = p + 1 by omega]
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show p + 1 - p = 1 by omega]
  rfl

/-- The increment block multiplies the packed value by `p`, leaving the
    scratch counter clear.

    The block opens with a no-op: a test of the scratch counter, which the
    precondition says is empty, so it always falls through to the next slot.
    That slot costs a step and nothing else, and it is what makes the block's
    run provably non-empty even when the block exits to its own base — which
    happens whenever a source instruction jumps to itself. Without it there
    is no way to tell a self-looping block from one that never ran. -/
theorem incBlock_reaches (prog : Program) (p base exit : Nat) (hp : 0 < p)
    (hemb : EmbeddedAt prog base (incBlock p base exit)) :
    ∀ (s : State), s.pc = base → s.regs 1 = 0 →
      ∃ c, 1 ≤ c ∧ runFor prog c s = some
        { pc := exit, regs := fun i => if i = 0 then p * s.regs 0 else
          if i = 1 then 0 else s.regs i } := by
  intro s hpc hs1
  have hentry : prog[base]? = some (Instruction.jzdec 1 (base + 1) (base + 1)) := by
    simpa only [Nat.add_zero] using
      embeddedAt_get prog base _ hemb 0 _ (incBlock_get_entry p base exit)
  have h0 : prog[base + 1]? = some (Instruction.jzdec 0 (base + 2 + p) (base + 2)) :=
    embeddedAt_get prog base _ hemb 1 _ (incBlock_get_head p base exit)
  have hchain : ∀ j, j < p → prog[base + 2 + j]? =
      some (Instruction.inc 1 (if j + 1 = p then base + 1 else base + 3 + j)) := by
    intro j hj
    have h := embeddedAt_get prog base _ hemb (2 + j) _ (incBlock_get_chain p base exit j hj)
    rwa [← Nat.add_assoc] at h
  have hd0 : prog[base + 2 + p]? = some (Instruction.jzdec 1 exit (base + 2 + p + 1)) := by
    have h := embeddedAt_get prog base _ hemb (p + 2) _ (incBlock_get_drain0 p base exit)
    rwa [show base + (p + 2) = base + 2 + p by omega] at h
  have hd1 : prog[base + 2 + p + 1]? = some (Instruction.inc 0 (base + 2 + p)) := by
    have h := embeddedAt_get prog base _ hemb (p + 3) _ (incBlock_get_drain1 p base exit)
    rwa [show base + (p + 3) = base + 2 + p + 1 by omega] at h
  -- The entry no-op falls through, the scratch counter being empty.
  have hstep : step prog s = some { s with pc := base + 1 } := by
    simp only [step, hpc, hentry, hs1, if_pos]
  -- The scaled transfer empties counter zero into counter one, `p` at a time.
  have hkd := kdrain_reaches prog 0 1 (base + 1) (base + 2 + p) p (by omega) hp h0 hchain
    (s.regs 0) { s with pc := base + 1 } rfl rfl
  set s1 : State := scaled 0 1 (base + 2 + p) p (s.regs 0) { s with pc := base + 1 }
    with hs1def
  -- The drain pours it back, undoing only the displacement.
  have hdr := drain_reaches prog 1 0 (base + 2 + p) exit (by omega) hd0 hd1
    (s1.regs 1) s1 rfl rfl
  have hpath : Reaches prog { s with pc := base + 1 } (drained 1 0 exit (s1.regs 1) s1) :=
    reaches_trans hkd hdr
  -- The final register file: the packed value multiplied, the scratch clear.
  have hfinal : drained 1 0 exit (s1.regs 1) s1
      = { pc := exit, regs := fun i => if i = 0 then p * s.regs 0 else
          if i = 1 then 0 else s.regs i } := by
    refine State.ext rfl (funext fun r => ?_)
    by_cases hr1 : r = 1
    · subst hr1
      simp only [drained, hs1def, scaled, hs1, if_pos trivial,
        if_neg (by omega : ¬ (1 : Nat) = 0)]
    · by_cases hr0 : r = 0
      · subst hr0
        simp only [drained, hs1def, scaled, hs1, if_pos trivial,
          if_neg (by omega : ¬ (1 : Nat) = 0), if_neg (by omega : ¬ (0 : Nat) = 1)]
        omega
      · simp only [drained, hs1def, scaled, if_neg hr0, if_neg hr1]
  rw [hfinal] at hpath
  -- The entry no-op is the first step, so the count is positive whatever the
  -- rest of the path costs — the block's exit may be its own base.
  exact runFor_pos_of_step prog s _ _ hstep hpath

/-- One restore arm, for a remainder of `r`. The divide consumed the packed
    value; its quotient sits in the scratch counter and the remainder is
    recorded only in which exit was taken. Multiplying the quotient back up
    and adding `r` literal units rebuilds exactly what was there. -/
def restoreArm (p r base exit : Nat) : Program :=
  [Instruction.jzdec 1 (base + 1 + p) (base + 1)]
  ++ (List.range p).map (fun j =>
      Instruction.inc 0 (if j + 1 = p then base else base + 2 + j))
  ++ (List.range r).map (fun j =>
      Instruction.inc 0 (if j + 1 = r then exit else base + 1 + p + j + 1))

theorem restoreArm_length (p r base exit : Nat) :
    (restoreArm p r base exit).length = p + 1 + r := by
  simp only [restoreArm, List.length_append, List.length_cons, List.length_map,
    List.length_range, List.length_nil]
  omega

/-- A restore arm padded to a uniform length. The arms differ in size — arm
    `r` carries `r` literal units — which would make each one's address a
    running total over all the earlier ones. Padding them all to `2 * p` makes
    arm `r` start at a closed-form offset instead, and the padding is
    unreachable, `EmbeddedAt` constraining only the slots that are used. -/
def paddedArm (p r base exit : Nat) : Program :=
  restoreArm p r base exit ++ List.replicate (2 * p - (p + 1 + r)) Instruction.halt

theorem paddedArm_length (p r base exit : Nat) (hrp : r < p) :
    (paddedArm p r base exit).length = 2 * p := by
  simp only [paddedArm, List.length_append, restoreArm_length, List.length_replicate]
  omega

/-- The padding sits past the arm, so an embedded padded arm embeds the arm
    itself — which is what the effect lemma asks for. -/
theorem embeddedAt_paddedArm (prog : Program) (p r base exit : Nat)
    (h : EmbeddedAt prog base (paddedArm p r base exit)) :
    EmbeddedAt prog base (restoreArm p r base exit) :=
  embeddedAt_append_left prog base _ _ h

/-- Reading the restore arm's slots: the opening test, the multiply-back
    chain, and the literal units that add the remainder. -/
theorem restoreArm_get_head (p r base exit : Nat) :
    (restoreArm p r base exit)[0]? =
      some (Instruction.jzdec 1 (base + 1 + p) (base + 1)) := rfl

theorem restoreArm_get_chain (p r base exit j : Nat) (hj : j < p) :
    (restoreArm p r base exit)[1 + j]? =
      some (Instruction.inc 0 (if j + 1 = p then base else base + 2 + j)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.inc 0 (if j + 1 = p then base else base + 2 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [restoreArm, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show 1 + j - 1 = j by omega]
  rw [List.getElem?_append_left (by rw [hlen]; exact hj), List.getElem?_map,
    List.getElem?_range hj]
  rfl

theorem restoreArm_get_units (p r base exit j : Nat) (hj : j < r) :
    (restoreArm p r base exit)[1 + p + j]? =
      some (Instruction.inc 0 (if j + 1 = r then exit else base + 1 + p + j + 1)) := by
  have hlenp : ((List.range p).map (fun j =>
      Instruction.inc 0 (if j + 1 = p then base else base + 2 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [restoreArm, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show 1 + p + j - 1 = p + j by omega]
  rw [List.getElem?_append_right (by rw [hlenp]; omega), hlenp,
    show p + j - p = j by omega, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- Walking the arm's literal units from offset `j` adds the `r - j` that
    remain and lands on the exit. The chain is straight-line — every slot is
    an `inc` naming the next — so this is an induction on how many are
    left. `bumped` is the same shape the transfer loops use for a chain's
    effect, so the two compose without translation. -/
theorem restoreArm_units_reaches (prog : Program) (p r base exit : Nat)
    (hunits : ∀ j, j < r → prog[base + 1 + p + j]? =
      some (Instruction.inc 0 (if j + 1 = r then exit else base + 1 + p + j + 1))) :
    ∀ (d j : Nat), j + d = r → 0 < d → ∀ (s : State), s.pc = base + 1 + p + j →
      Reaches prog s (bumped 0 d exit s) := by
  intro d
  induction d with
  | zero => intro j _ hd; omega
  | succ m ih =>
      intro j hjr _ s hpc
      have hjlt : j < r := by omega
      have hstep : step prog s
          = some (bumped 0 1 (if j + 1 = r then exit else base + 1 + p + j + 1) s) := by
        simp only [step, hpc, hunits j hjlt, setReg, bumped]
      by_cases hlast : j + 1 = r
      · -- The last unit jumps straight to the exit.
        have hm : m = 0 := by omega
        subst hm
        rw [if_pos hlast] at hstep
        refine Reaches.step _ _ _ hstep ?_
        have heq : bumped 0 1 exit s = bumped 0 (0 + 1) exit s := by
          rw [Nat.zero_add]
        rw [heq]
        exact Reaches.refl _
      · -- Otherwise the chain continues one slot along.
        rw [if_neg hlast] at hstep
        refine Reaches.step _ _ _ hstep ?_
        have hrec := ih (j + 1) (by omega) (by omega)
          (bumped 0 1 (base + 1 + p + j + 1) s)
          (by simp only [bumped]; omega)
        -- Two bumps of one and `m` are a single bump of `m + 1`.
        have heq : bumped 0 m exit (bumped 0 1 (base + 1 + p + j + 1) s)
            = bumped 0 (m + 1) exit s := by
          refine State.ext rfl (funext fun q => ?_)
          by_cases hq : q = 0
          · subst hq
            rw [bumped_regs_self, bumped_regs_self, bumped_regs_self]
            omega
          · rw [bumped_regs_other _ _ _ _ _ hq, bumped_regs_other _ _ _ _ _ hq,
              bumped_regs_other _ _ _ _ _ hq]
        rw [← heq]
        exact hrec

/-- The state a restore arm leaves: the packed value rebuilt from its
    quotient and remainder, the scratch counter emptied. -/
def restored (r exit : Nat) (p : Nat) (s : State) : State :=
  { pc := exit,
    regs := fun i => if i = 0 then p * s.regs 1 + r else if i = 1 then 0 else s.regs i }

/-- The restore arm rebuilds the packed value the divide destroyed. The
    scaled transfer multiplies the quotient back up by `p`, and the literal
    units add the remainder, giving `p * q + r` — which is what the counter
    held before the divide consumed it. -/
theorem restoreArm_reaches (prog : Program) (p r base exit : Nat) (hp : 0 < p) (hr : 0 < r)
    (hemb : EmbeddedAt prog base (restoreArm p r base exit)) :
    ∀ (s : State), s.pc = base → s.regs 0 = 0 →
      Reaches prog s (restored r exit p s) := by
  intro s hpc hs0
  have h0 : prog[base]? = some (Instruction.jzdec 1 (base + 1 + p) (base + 1)) := by
    simpa only [Nat.add_zero] using
      embeddedAt_get prog base _ hemb 0 _ (restoreArm_get_head p r base exit)
  have hchain : ∀ j, j < p → prog[base + 1 + j]? =
      some (Instruction.inc 0 (if j + 1 = p then base else base + 2 + j)) := by
    intro j hj
    have h := embeddedAt_get prog base _ hemb (1 + j) _ (restoreArm_get_chain p r base exit j hj)
    rwa [← Nat.add_assoc] at h
  have hunits : ∀ j, j < r → prog[base + 1 + p + j]? =
      some (Instruction.inc 0 (if j + 1 = r then exit else base + 1 + p + j + 1)) := by
    intro j hj
    have h := embeddedAt_get prog base _ hemb (1 + p + j) _
      (restoreArm_get_units p r base exit j hj)
    rwa [← Nat.add_assoc, ← Nat.add_assoc] at h
  -- The scaled transfer pours the quotient back, `p` units at a time.
  have hkd := kdrain_reaches prog 1 0 base (base + 1 + p) p (by omega) hp h0 hchain
    (s.regs 1) s hpc rfl
  set s1 : State := scaled 1 0 (base + 1 + p) p (s.regs 1) s with hs1def
  -- Then the literal units add the remainder.
  have hu := restoreArm_units_reaches prog p r base exit hunits r 0 (by omega) hr s1
    (by simp only [hs1def, scaled]; omega)
  -- The two together leave `p * q + r` in the packed counter.
  have heq : bumped 0 r exit s1 = restored r exit p s := by
    refine State.ext rfl (funext fun q => ?_)
    simp only [restored]
    by_cases hq0 : q = 0
    · subst hq0
      rw [bumped_regs_self]
      simp only [hs1def, scaled, if_neg (by omega : ¬ (0 : Nat) = 1), hs0, if_pos trivial]
      omega
    · rw [bumped_regs_other _ _ _ _ _ hq0]
      simp only [hs1def, scaled, if_neg hq0]
  rw [← heq]
  exact reaches_trans hkd hu

end Register

end LeanBF
