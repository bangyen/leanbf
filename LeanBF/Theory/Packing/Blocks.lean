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
* `incBlockLen`: Its length.

## Theorems

* `incBlock_get_head`: The block's opening test.
* `incBlock_get_chain`: The block's increment chain.
* `incBlock_get_drain0`: The drain loop's test.
* `incBlock_get_drain1`: The drain loop's increment.
* `incBlock_reaches`: The increment block multiplies by the register's prime.
-/

namespace LeanBF

namespace Register

/-- The block that increments a packed register: move the packed value into
    the scratch counter `p` units at a time, then pour it back. The scaled
    transfer is the multiplication; the drain only undoes the displacement. -/
def incBlock (p base exit : Nat) : Program :=
  [Instruction.jzdec 0 (base + 1 + p) (base + 1)]
  ++ (List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base else base + 2 + j))
  ++ [Instruction.jzdec 1 exit (base + 1 + p + 1), Instruction.inc 0 (base + 1 + p)]

theorem incBlockLen (p base exit : Nat) : (incBlock p base exit).length = p + 3 := by
  simp only [incBlock, List.length_append, List.length_cons, List.length_map,
    List.length_range, List.length_nil]
  omega

/-- Reading the increment block's slots. The block is three pieces appended,
    so indexing it is a case split on which piece the offset lands in; doing
    that once here keeps it out of the effect proof. -/
theorem incBlock_get_head (p base exit : Nat) :
    (incBlock p base exit)[0]? = some (Instruction.jzdec 0 (base + 1 + p) (base + 1)) := rfl

theorem incBlock_get_chain (p base exit j : Nat) (hj : j < p) :
    (incBlock p base exit)[1 + j]? =
      some (Instruction.inc 1 (if j + 1 = p then base else base + 2 + j)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base else base + 2 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [incBlock, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show 1 + j - 1 = j by omega]
  rw [List.getElem?_append_left (by rw [hlen]; exact hj), List.getElem?_map,
    List.getElem?_range hj]
  rfl

theorem incBlock_get_drain0 (p base exit : Nat) :
    (incBlock p base exit)[p + 1]? =
      some (Instruction.jzdec 1 exit (base + 1 + p + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base else base + 2 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [incBlock, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show p + 1 - 1 = p by omega]
  rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

theorem incBlock_get_drain1 (p base exit : Nat) :
    (incBlock p base exit)[p + 2]? = some (Instruction.inc 0 (base + 1 + p)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.inc 1 (if j + 1 = p then base else base + 2 + j))).length = p := by
    rw [List.length_map, List.length_range]
  rw [incBlock, List.append_assoc,
    List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil, show p + 2 - 1 = p + 1 by omega]
  rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show p + 1 - p = 1 by omega]
  rfl

/-- The increment block multiplies the packed value by `p`, leaving the
    scratch counter clear. The step count is positive because the opening
    `jzdec` executes whatever the counter holds. -/
theorem incBlock_reaches (prog : Program) (p base exit : Nat) (hp : 0 < p)
    (hne : base ≠ exit) (hemb : EmbeddedAt prog base (incBlock p base exit)) :
    ∀ (s : State), s.pc = base → s.regs 1 = 0 →
      ∃ c, 1 ≤ c ∧ runFor prog c s = some
        { pc := exit, regs := fun i => if i = 0 then p * s.regs 0 else
          if i = 1 then 0 else s.regs i } := by
  intro s hpc hs1
  have h0 : prog[base]? = some (Instruction.jzdec 0 (base + 1 + p) (base + 1)) := by
    simpa only [Nat.add_zero] using
      embeddedAt_get prog base _ hemb 0 _ (incBlock_get_head p base exit)
  have hchain : ∀ j, j < p → prog[base + 1 + j]? =
      some (Instruction.inc 1 (if j + 1 = p then base else base + 2 + j)) := by
    intro j hj
    have h := embeddedAt_get prog base _ hemb (1 + j) _ (incBlock_get_chain p base exit j hj)
    rwa [← Nat.add_assoc] at h
  -- The scaled transfer empties counter zero into counter one, `p` at a time.
  have hkd := kdrain_reaches prog 0 1 base (base + 1 + p) p (by omega) hp h0 hchain
    (s.regs 0) s hpc rfl
  set s1 : State := scaled 0 1 (base + 1 + p) p (s.regs 0) s with hs1def
  -- The drain pours it back, undoing only the displacement.
  have hd0 : prog[base + 1 + p]? = some (Instruction.jzdec 1 exit (base + 1 + p + 1)) := by
    have h := embeddedAt_get prog base _ hemb (p + 1) _ (incBlock_get_drain0 p base exit)
    rwa [show base + (p + 1) = base + 1 + p by omega] at h
  have hd1 : prog[base + 1 + p + 1]? = some (Instruction.inc 0 (base + 1 + p)) := by
    have h := embeddedAt_get prog base _ hemb (p + 2) _ (incBlock_get_drain1 p base exit)
    rwa [show base + (p + 2) = base + 1 + p + 1 by omega] at h
  have hdr := drain_reaches prog 1 0 (base + 1 + p) exit (by omega) hd0 hd1
    (s1.regs 1) s1 rfl rfl
  -- The two loops compose into the whole block's path.
  have hpath : Reaches prog s (drained 1 0 exit (s1.regs 1) s1) := reaches_trans hkd hdr
  -- The final register file: the packed value multiplied, the scratch clear.
  have hfinal : drained 1 0 exit (s1.regs 1) s1
      = { pc := exit, regs := fun i => if i = 0 then p * s.regs 0 else
          if i = 1 then 0 else s.regs i } := by
    refine State.ext rfl (funext fun r => ?_)
    by_cases hr1 : r = 1
    · -- The scratch counter was filled by the transfer and emptied by the drain.
      subst hr1
      simp only [drained, hs1def, scaled, hs1, if_pos trivial,
        if_neg (by omega : ¬ (1 : Nat) = 0)]
    · by_cases hr0 : r = 0
      · -- Counter zero was emptied, then refilled with the scaled amount.
        subst hr0
        simp only [drained, hs1def, scaled, hs1, if_pos trivial,
          if_neg (by omega : ¬ (1 : Nat) = 0), if_neg (by omega : ¬ (0 : Nat) = 1)]
        omega
      · simp only [drained, hs1def, scaled, if_neg hr0, if_neg hr1]
  rw [hfinal] at hpath
  -- The opening `jzdec` executes whatever the counter holds, so the count
  -- is positive however short the rest of the path turns out to be.
  -- The block exits past itself, so the counter moved and the run is not
  -- empty. That is the positivity the divergence argument will consume.
  exact runFor_pos_of_reaches prog s _ (by rw [hpc]; exact hne) hpath

end Register

end LeanBF
