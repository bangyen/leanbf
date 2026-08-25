/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing.Blocks

/-!
# The Conditional Block

What a `jzdec` becomes once the register file is a single number.

Testing a packed register and decrementing it are the same operation. The
register is non-zero exactly when its prime divides the packed value, and the
decrement is that division — so one divide loop answers the test and performs
the update at once, branching by which remainder it exits on. That is the
same economy the search tail found, where a single `jzdec` both detected
success and decoded it.

The layout has four parts after the entry no-op:

* the divide loop, whose `p` exits are contiguous by construction;
* a jump table of `p` slots, one per remainder, each an unconditional jump —
  the divide leaves the packed counter empty, so a test of it always takes
  the zero branch, which is how a machine with no plain jump makes one;
* the drain, taken on remainder zero, which pours the quotient back and
  leaves for `ifNonZero`;
* the restore arms, one per non-zero remainder, each padded to `2 * p` so its
  address is a closed form rather than a sum over the arms before it.

The jump table exists because `div_reaches` puts its exits at consecutive
addresses, while the destinations they stand for are spread out. Rather than
weaken that lemma, the table absorbs the difference in one slot each.

## Main definitions

* `jzdecHead`: The block's pieces before the restore arms.
* `jzdecArms`: The restore arms, laid end to end.
* `dividedAt`: The state the divide leaves at a handler's door.
* `jzdecBlock`: The block that tests and decrements a packed register.

## Theorems

* `jzdecHead_length`: The head's length.
* `jzdecArms_length`: The arms' total length.
* `jzdecBlockLen`: The block's length.
* `jzdecBlock_get_head`: A low slot is read from the head.
* `jzdecHead_get_entry`: The block's entry no-op.
* `jzdecHead_get_div`: The divide loop's test chain.
* `jzdecHead_get_divInc`: The divide loop's increment.
* `jzdecHead_get_table`: The jump table.
* `jzdecHead_get_drain0`: The drain's test.
* `jzdecHead_get_drain1`: The drain's increment.
* `jzdecBlock_common`: The path both branches share.
* `jzdecBlock_dvd`: A register that was non-zero is decremented.
-/

namespace LeanBF

namespace Register

/-- Where a remainder's handler begins: the drain for zero, and otherwise the
    arm for that remainder, the arms being uniformly `2 * p` long. -/
def jzdecDest (p base r : Nat) : Nat :=
  if r = 0 then base + 2 + 2 * p else base + 2 + 2 * p + 2 + (r - 1) * (2 * p)

/-- Everything before the restore arms: the entry no-op, the divide loop,
    the jump table, and the drain. Naming it lets a slot lookup split the
    block once rather than peeling four appends. -/
def jzdecHead (p base ifNonZero : Nat) : Program :=
  Instruction.jzdec 1 (base + 1) (base + 1)
  :: ((List.range p).map (fun j =>
        Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))
      ++ Instruction.inc 1 (base + 1)
        :: ((List.range p).map (fun r =>
              Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))
            ++ [Instruction.jzdec 1 ifNonZero (base + 2 + 2 * p + 1),
                Instruction.inc 0 (base + 2 + 2 * p)]))

theorem jzdecHead_length (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero).length = 2 + 2 * p + 2 := by
  simp only [jzdecHead, List.length_cons, List.length_append, List.length_map,
    List.length_range, List.length_nil]
  omega

/-- The arms, laid end to end, each padded to the same length. -/
def jzdecArms (p base ifZero : Nat) : Program :=
  (List.range (p - 1)).flatMap (fun i =>
    paddedArm p (i + 1) (base + 2 + 2 * p + 2 + i * (2 * p)) ifZero)

theorem jzdecArms_length (p base ifZero : Nat) :
    (jzdecArms p base ifZero).length = (p - 1) * (2 * p) := by
  rw [jzdecArms, List.length_flatMap]
  have hconst : ∀ i ∈ List.range (p - 1),
      (paddedArm p (i + 1) (base + 2 + 2 * p + 2 + i * (2 * p)) ifZero).length = 2 * p := by
    intro i hi
    exact paddedArm_length p (i + 1) _ _ (by have := List.mem_range.mp hi; omega)
  rw [List.map_congr_left hconst, List.map_const', List.sum_replicate_nat,
    List.length_range]

/-- The block that tests and decrements a packed register. -/
def jzdecBlock (p base ifZero ifNonZero : Nat) : Program :=
  jzdecHead p base ifNonZero ++ jzdecArms p base ifZero

theorem jzdecBlockLen (p base ifZero ifNonZero : Nat) :
    (jzdecBlock p base ifZero ifNonZero).length = 2 + 2 * p + 2 + (p - 1) * (2 * p) := by
  rw [jzdecBlock, List.length_append, jzdecHead_length, jzdecArms_length]

/-- Reading the block's slots. Everything below `2 + 2 * p + 2` lives in the
    head, so one split sends the lookup to the right piece. -/
theorem jzdecBlock_get_head (p base ifZero ifNonZero j : Nat) (hj : j < 2 + 2 * p + 2) :
    (jzdecBlock p base ifZero ifNonZero)[j]? = (jzdecHead p base ifNonZero)[j]? := by
  rw [jzdecBlock, List.getElem?_append_left (by rw [jzdecHead_length]; exact hj)]

theorem jzdecHead_get_entry (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[0]? =
      some (Instruction.jzdec 1 (base + 1) (base + 1)) := rfl

theorem jzdecHead_get_div (p base ifNonZero j : Nat) (hj : j < p) :
    (jzdecHead p base ifNonZero)[1 + j]? =
      some (Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 1 + j = j + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by rw [hlen]; exact hj), List.getElem?_map,
    List.getElem?_range hj]
  rfl

theorem jzdecHead_get_divInc (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[1 + p]? = some (Instruction.inc 1 (base + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 1 + p = p + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

theorem jzdecHead_get_table (p base ifNonZero r : Nat) (hr : r < p) :
    (jzdecHead p base ifNonZero)[2 + p + r]? =
      some (Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  have hlen2 : ((List.range p).map (fun r =>
      Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 2 + p + r = (p + r + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show p + r + 1 - p = r + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by rw [hlen2]; exact hr), List.getElem?_map,
    List.getElem?_range hr]
  rfl

theorem jzdecHead_get_drain0 (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[2 + 2 * p]? =
      some (Instruction.jzdec 1 ifNonZero (base + 2 + 2 * p + 1)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  have hlen2 : ((List.range p).map (fun r =>
      Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 2 + 2 * p = (2 * p + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show 2 * p + 1 - p = p + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen2]), hlen2, Nat.sub_self]
  rfl

theorem jzdecHead_get_drain1 (p base ifNonZero : Nat) :
    (jzdecHead p base ifNonZero)[2 + 2 * p + 1]? =
      some (Instruction.inc 0 (base + 2 + 2 * p)) := by
  have hlen : ((List.range p).map (fun j =>
      Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1))).length = p := by
    rw [List.length_map, List.length_range]
  have hlen2 : ((List.range p).map (fun r =>
      Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r))).length = p := by
    rw [List.length_map, List.length_range]
  rw [jzdecHead, show 2 + 2 * p + 1 = (2 * p + 2) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen]; omega), hlen,
    show 2 * p + 2 - p = p + 2 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [hlen2]; omega), hlen2,
    show p + 1 - p = 1 by omega]
  rfl

/-- The state the divide leaves at a handler's door: the packed counter
    emptied, the quotient held in the scratch. -/
def dividedAt (p pc v : Nat) (s : State) : State :=
  { pc := pc, regs := fun i => if i = 0 then 0 else if i = 1 then v / p else s.regs i }

/-- The path both branches share: fall through the entry no-op, divide the
    packed value by `p`, and take the jump table's slot for the remainder.
    The table entry is an unconditional jump, the divide having emptied the
    counter it tests. -/
theorem jzdecBlock_common (prog : Program) (p base ifZero ifNonZero : Nat) (hp : 0 < p)
    (hemb : EmbeddedAt prog base (jzdecBlock p base ifZero ifNonZero)) :
    ∀ (s : State), s.pc = base → s.regs 1 = 0 →
      ∃ s₁, step prog s = some s₁ ∧
        Reaches prog s₁
          (dividedAt p (jzdecDest p base (s.regs 0 % p)) (s.regs 0) s) := by
  intro s hpc hs1
  have hg : ∀ j, j < 2 + 2 * p + 2 → ∀ i, (jzdecHead p base ifNonZero)[j]? = some i →
      prog[base + j]? = some i := by
    intro j hj i hi
    exact embeddedAt_get prog base _ hemb j i (by
      rw [jzdecBlock_get_head p base ifZero ifNonZero j hj]
      exact hi)
  -- The entry no-op falls through, the scratch counter being empty.
  have hentry : prog[base]? = some (Instruction.jzdec 1 (base + 1) (base + 1)) := by
    simpa only [Nat.add_zero] using hg 0 (by omega) _ (jzdecHead_get_entry p base ifNonZero)
  have hstep : step prog s = some { s with pc := base + 1 } := by
    simp only [step, hpc, hentry, hs1, if_pos]
  refine ⟨_, hstep, ?_⟩
  -- The divide loop's chain and its increment.
  have hchain : ∀ j, j < p → prog[base + 1 + j]? =
      some (Instruction.jzdec 0 (base + 2 + p + j) (base + 1 + j + 1)) := by
    intro j hj
    have h := hg (1 + j) (by omega) _ (jzdecHead_get_div p base ifNonZero j hj)
    rwa [← Nat.add_assoc] at h
  have hinc : prog[base + 1 + p]? = some (Instruction.inc 1 (base + 1)) := by
    have h := hg (1 + p) (by omega) _ (jzdecHead_get_divInc p base ifNonZero)
    rwa [← Nat.add_assoc] at h
  -- The divide consumes the packed value, exiting on its remainder.
  have hdiv := div_reaches prog 0 1 (base + 1) (base + 2 + p) p (by omega)
    (by
      intro j hj
      rw [hchain j hj])
    hinc (s.regs 0 / p) (s.regs 0 % p) (Nat.mod_lt _ hp)
    { s with pc := base + 1 } rfl (by
      change s.regs 0 = p * (s.regs 0 / p) + s.regs 0 % p
      exact (Nat.div_add_mod (s.regs 0) p).symm)
  set r : Nat := s.regs 0 % p with hrdef
  set s2 : State := divided 0 1 (base + 2 + p) (s.regs 0 / p) r { s with pc := base + 1 }
    with hs2def
  -- The table slot for that remainder is an unconditional jump.
  have htab : prog[base + 2 + p + r]? =
      some (Instruction.jzdec 0 (jzdecDest p base r) (jzdecDest p base r)) := by
    have hrp : r < p := by rw [hrdef]; exact Nat.mod_lt _ hp
    have h := hg (2 + p + r) (by omega) _
      (jzdecHead_get_table p base ifNonZero r hrp)
    rwa [← Nat.add_assoc, ← Nat.add_assoc] at h
  have hzero : s2.regs 0 = 0 := by
    simp only [hs2def, divided, if_pos trivial]
  have hjump : step prog s2 = some { s2 with pc := jzdecDest p base r } := by
    have hpc2 : s2.pc = base + 2 + p + r := by simp only [hs2def, divided]
    rw [step, hpc2, htab]
    simp only [hzero, if_pos]
  refine reaches_trans hdiv (Reaches.step _ _ _ hjump ?_)
  -- The state after the jump is the divide's result at the handler's address.
  have hfin : ({ s2 with pc := jzdecDest p base r } : State)
      = dividedAt p (jzdecDest p base r) (s.regs 0) s := by
    refine State.ext rfl (funext fun q => ?_)
    simp only [hs2def, divided, dividedAt]
    by_cases hq0 : q = 0
    · rw [if_pos hq0, if_pos hq0]
    · rw [if_neg hq0, if_neg hq0]
      by_cases hq1 : q = 1
      · rw [if_pos hq1, if_pos hq1, hs1]
        omega
      · rw [if_neg hq1, if_neg hq1]
  rw [hfin]
  exact Reaches.refl _

/-- The register was non-zero: its prime divides the packed value, the
    quotient is the decremented file, and the drain pours it back before
    leaving for `ifNonZero`. -/
theorem jzdecBlock_dvd (prog : Program) (p base ifZero ifNonZero : Nat) (hp : 0 < p)
    (hemb : EmbeddedAt prog base (jzdecBlock p base ifZero ifNonZero)) :
    ∀ (s : State), s.pc = base → s.regs 1 = 0 → p ∣ s.regs 0 →
      ∃ c, 1 ≤ c ∧ runFor prog c s = some
        { pc := ifNonZero, regs := fun i => if i = 0 then s.regs 0 / p
          else if i = 1 then 0 else s.regs i } := by
  intro s hpc hs1 hdvd
  have hg : ∀ j, j < 2 + 2 * p + 2 → ∀ i, (jzdecHead p base ifNonZero)[j]? = some i →
      prog[base + j]? = some i := by
    intro j hj i hi
    exact embeddedAt_get prog base _ hemb j i (by
      rw [jzdecBlock_get_head p base ifZero ifNonZero j hj]
      exact hi)
  -- The remainder is zero, so the table sends the run to the drain.
  have hrem : s.regs 0 % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rcases jzdecBlock_common prog p base ifZero ifNonZero hp hemb s hpc hs1 with
    ⟨s₁, hstep, hreach⟩
  rw [hrem] at hreach
  have hdest : jzdecDest p base 0 = base + 2 + 2 * p := by
    simp only [jzdecDest, if_pos trivial]
  rw [hdest] at hreach
  -- The drain pours the quotient back into the packed counter.
  have hd0 : prog[base + 2 + 2 * p]? =
      some (Instruction.jzdec 1 ifNonZero (base + 2 + 2 * p + 1)) := by
    have h := hg (2 + 2 * p) (by omega) _ (jzdecHead_get_drain0 p base ifNonZero)
    rwa [← Nat.add_assoc] at h
  have hd1 : prog[base + 2 + 2 * p + 1]? =
      some (Instruction.inc 0 (base + 2 + 2 * p)) := by
    have h := hg (2 + 2 * p + 1) (by omega) _ (jzdecHead_get_drain1 p base ifNonZero)
    rwa [← Nat.add_assoc, ← Nat.add_assoc] at h
  set s2 : State := dividedAt p (base + 2 + 2 * p) (s.regs 0) s with hs2def
  have hdr := drain_reaches prog 1 0 (base + 2 + 2 * p) ifNonZero (by omega) hd0 hd1
    (s2.regs 1) s2 rfl rfl
  -- What the drain leaves: the quotient in the packed counter, scratch clear.
  have hfinal : drained 1 0 ifNonZero (s2.regs 1) s2
      = { pc := ifNonZero, regs := fun i => if i = 0 then s.regs 0 / p
          else if i = 1 then 0 else s.regs i } := by
    refine State.ext rfl (funext fun q => ?_)
    by_cases hq1 : q = 1
    · subst hq1
      simp only [drained, hs2def, dividedAt, if_pos trivial,
        if_neg (by omega : ¬ (1 : Nat) = 0)]
    · by_cases hq0 : q = 0
      · subst hq0
        simp only [drained, hs2def, dividedAt, if_pos trivial,
          if_neg (by omega : ¬ (1 : Nat) = 0), if_neg (by omega : ¬ (0 : Nat) = 1),
          Nat.zero_add]
      · simp only [drained, hs2def, dividedAt, if_neg hq0, if_neg hq1]
  rw [← hfinal]
  exact runFor_pos_of_step prog s s₁ _ hstep (reaches_trans hreach hdr)

end Register

end LeanBF
