/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Universal.Convention

/-!
# Relocatable Fragment Builders

The form the induction over `Nat.Primrec` actually inducts on. `Computes`
pins a fragment to one program at one base address, but the `comp`, `pair`,
and `prec` cases each need two independently constructed fragments to sit
inside a *single* program, one after the other. Two `RegComputable`
witnesses cannot be combined: each existentially binds its own program, and
the jump targets inside those programs are absolute.

The fix is to induct on a builder rather than on a program. `Builds f` says
that for every base address there is a fragment which, wherever it is
embedded, computes `f` from that base. Concatenating two builders is then
just list append, and the second one is handed `base + (first).length` so
the absolute targets it emits are already correct. Nothing is shifted after
the fact.

`EmbeddedAt` is the embedding relation, deliberately weaker than "`p` equals
`frag`": it only constrains the slots the fragment occupies, so the same `p`
can host several fragments at once. `embeddedAt_append_left` and
`embeddedAt_append_right` split one embedding of a concatenation into the two
embeddings its halves need, which is what lets both fragment specifications
be instantiated at the same `p`.

The scratch region's upper end is existential, because each builder needs a
different amount of scratch.

`computes_seq_clear` is the composition vehicle. `computes_seq` cannot be:
it places the midpoint register inside the scratch region both fragments
see, so its postcondition demands that register hold the first function's
output *and* be zero, which only a vanishing function satisfies. Splitting
the region — the caller sees `[lo, hi)`, the sub-fragments `[lo + 1, hi)` —
gives the midpoint its initial zero from the caller while letting it carry
a real value between the halves, and a final clear restores the wide
contract.

`computes_mono_hi` reconciles two such choices:
a fragment that leaves `[lo, hi)` clear also leaves the larger `[lo, hi')`
clear, since the registers between are outside its scratch and its frame
clause says it never touched them. That is why the motive fixes the named
registers *below* `lo` rather than allowing them above `hi` — with `hi`
varying, `hi ≤ inR` would not survive the widening.

## Main definitions

* `EmbeddedAt`: A fragment occupies a program's slots at a base address.
* `Builds`: A relocatable builder computing a function at any base.

## Theorems

* `embeddedAt_get`: Reading one slot of an embedded fragment.
* `embeddedAt_append_left`: The first half of an embedded concatenation.
* `embeddedAt_append_right`: The second half of an embedded concatenation.
* `computes_mono_hi`: Widening the scratch region preserves computation.
* `computes_seq_clear`: Sequencing through a midpoint register, then
  clearing it.
* `builds_comp`: Builders compose, giving the `comp` case.
* `builds_zero`: The empty builder computes the constant zero.
* `builds_succ`: A six-slot fragment computes the successor.
-/

namespace LeanBF

namespace Register

/-- The fragment `frag` occupies the slots `[base, base + frag.length)` of
    `p`. Only those slots are constrained, so one program can host many
    fragments side by side. -/
def EmbeddedAt (p : Program) (base : Nat) (frag : Program) : Prop :=
  ∀ j, j < frag.length → p[base + j]? = frag[j]?

/-- Reading one slot of an embedded fragment. The `EmbeddedAt` hypothesis
    speaks in offsets from the base, while the fragment lemmas want absolute
    addresses, so this is the bridge every concrete builder crosses. -/
theorem embeddedAt_get (p : Program) (base : Nat) (frag : Program) (h : EmbeddedAt p base frag)
    (j : Nat) (i : Instruction) (hj : frag[j]? = some i) : p[base + j]? = some i := by
  have hlt : j < frag.length := by
    by_contra hc
    rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hc)] at hj
    exact absurd hj (by simp only [reduceCtorEq, not_false_eq_true])
  rw [h j hlt]
  exact hj

theorem embeddedAt_append_left (p : Program) (base : Nat) (A B : Program)
    (h : EmbeddedAt p base (A ++ B)) : EmbeddedAt p base A := by
  intro j hj
  have hlt : j < (A ++ B).length := by
    rw [List.length_append]
    omega
  rw [h j hlt, List.getElem?_append_left hj]

theorem embeddedAt_append_right (p : Program) (base : Nat) (A B : Program)
    (h : EmbeddedAt p base (A ++ B)) : EmbeddedAt p (base + A.length) B := by
  intro j hj
  have hlt : A.length + j < (A ++ B).length := by
    rw [List.length_append]
    omega
  have hidx : base + A.length + j = base + (A.length + j) := by omega
  rw [hidx, h (A.length + j) hlt,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- Widening the scratch region: registers between the old and new upper ends
    lie outside the fragment's scratch, so its frame clause keeps them at the
    zero they started from. -/
theorem computes_mono_hi (p : Program) (base exit inR outR lo hi hi' : Nat) (f : Nat → Nat)
    (hle : hi ≤ hi') (hout : outR < lo)
    (hc : Computes p base exit inR outR lo hi f) :
    Computes p base exit inR outR lo hi' f := by
  intro s hpc hout0 hzero
  rcases hc s hpc hout0 (fun r hlo hhi => hzero r hlo (by omega)) with
    ⟨s', hr, hpc', hval, hin', hz, hfr⟩
  refine ⟨s', hr, hpc', hval, hin', ?_, fun r hro hlohi => hfr r hro (by omega)⟩
  intro r hlo hhi'
  by_cases hhi : r < hi
  · exact hz r hlo hhi
  · -- Outside the old scratch: untouched, so still the zero it started at.
    rw [hfr r (by omega) (Or.inr (by omega))]
    exact hzero r hlo hhi'

/-- A relocatable builder for `f`: for every choice of distinct named
    registers below the scratch region and every base address, some fragment
    computes `f` from that base wherever it is embedded, exiting just past
    itself. -/
def Builds (f : Nat → Nat) : Prop :=
  ∀ (inR outR lo : Nat), inR ≠ outR → inR < lo → outR < lo →
    ∀ (base : Nat), ∃ (hi : Nat) (frag : Program),
      lo ≤ hi ∧ ∀ (p : Program), EmbeddedAt p base frag →
        Computes p base (base + frag.length) inR outR lo hi f

/-- Sequencing with a cleanup: `g` computes into `midR`, `f` reads `midR`
    and computes into `outR`, and a final clear empties `midR`.

    `midR` is the bottom of the scratch region, and the two sub-fragments are
    given the narrower region `[lo + 1, hi)` that excludes it. That split is
    what makes composition work at all. `computes_seq` instead keeps `midR`
    inside the region both fragments see, so its postcondition demands that
    `midR` hold `g`'s output *and* be zero — satisfiable only when `g`
    vanishes. Here the caller's precondition still zeroes `midR`, because it
    is in the wide region, while neither sub-fragment claims it is zero on
    exit. The clear at the end restores the wide contract. -/
theorem computes_seq_clear (p : Program) (base mid clr exit inR outR lo hi : Nat)
    (f g : Nat → Nat)
    (hio : inR ≠ outR) (hilo : inR < lo) (holo : outR < lo) (hlohi : lo < hi)
    (hclr : p[clr]? = some (Instruction.jzdec lo exit clr))
    (hg : Computes p base mid inR lo (lo + 1) hi g)
    (hf : Computes p mid clr lo outR (lo + 1) hi f) :
    Computes p base exit inR outR lo hi (fun n => f (g n)) := by
  intro s hpc hout0 hzero
  have hnarrow : ∀ r, lo + 1 ≤ r → r < hi → s.regs r = 0 :=
    fun r h1 h2 => hzero r (by omega) h2
  rcases hg s hpc (hzero lo (le_refl _) hlohi) hnarrow with
    ⟨s1, hr1, hpc1, hval1, hin1, hz1, hfr1⟩
  -- `outR` sits below `lo`, outside `g`'s region, and is not `g`'s output.
  have hout1 : s1.regs outR = 0 := by
    rw [hfr1 outR (by omega) (by omega)]
    exact hout0
  rcases hf s1 hpc1 hout1 hz1 with ⟨s2, hr2, hpc2, hval2, hin2, hz2, hfr2⟩
  -- The clear empties `midR`, restoring the wide scratch contract.
  refine ⟨{ pc := exit, regs := fun i => if i = lo then 0 else s2.regs i },
    reaches_trans hr1 (reaches_trans hr2
      (clear_reaches p lo clr exit hclr (s2.regs lo) s2 hpc2 rfl)), rfl, ?_, ?_, ?_, ?_⟩
  · simp only []
    rw [if_neg (by omega : outR ≠ lo), hval2, hval1]
  · simp only []
    rw [if_neg (by omega : inR ≠ lo), hfr2 inR (by omega) (by omega), hin1]
  · intro r hlor hrhi
    simp only []
    by_cases hrlo : r = lo
    · rw [if_pos hrlo]
    · rw [if_neg hrlo]
      exact hz2 r (by omega) hrhi
  · intro r hro hrlohi
    simp only []
    rw [if_neg (by omega : r ≠ lo), hfr2 r hro (by omega), hfr1 r (by omega) (by omega)]

/-- Builders compose: place `g`'s fragment, then `f`'s, then a one-slot
    clear. The midpoint register is `lo`, the bottom of the caller's scratch,
    so the caller's precondition already zeroes it; the sub-builders are
    given the raised floor `lo + 1`, which keeps it out of their scratch and
    lets it carry `g`'s output between them. -/
theorem builds_comp (f g : Nat → Nat) (hf : Builds f) (hg : Builds g) :
    Builds (fun n => f (g n)) := by
  intro inR outR lo hio hin hout base
  rcases hg inR lo (lo + 1) (by omega) (by omega) (by omega) base with ⟨hiG, fragG, hloG, hG⟩
  rcases hf lo outR (lo + 1) (by omega) (by omega) (by omega)
    (base + fragG.length) with ⟨hiF, fragF, hloF, hF⟩
  -- The clear instruction jumps past itself when `lo` is empty.
  refine ⟨max hiG hiF,
    fragG ++ fragF ++ [Instruction.jzdec lo (base + fragG.length + fragF.length + 1)
      (base + fragG.length + fragF.length)], by omega, fun p hemb => ?_⟩
  have hembAB := embeddedAt_append_left p base (fragG ++ fragF) _ hemb
  have hembG := hG p (embeddedAt_append_left p base fragG fragF hembAB)
  have hembF := hF p (embeddedAt_append_right p base fragG fragF hembAB)
  have hclr : p[base + fragG.length + fragF.length]?
      = some (Instruction.jzdec lo (base + fragG.length + fragF.length + 1)
        (base + fragG.length + fragF.length)) := by
    have h := embeddedAt_append_right p base (fragG ++ fragF) _ hemb 0
      (by simp only [List.length_cons, List.length_nil]; omega)
    rw [List.length_append] at h
    simpa only [Nat.add_zero, Nat.add_assoc] using h
  have hlen : base + (fragG ++ fragF ++ [Instruction.jzdec lo
      (base + fragG.length + fragF.length + 1)
      (base + fragG.length + fragF.length)]).length
      = base + fragG.length + fragF.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [hlen]
  refine computes_seq_clear p base (base + fragG.length) (base + fragG.length + fragF.length)
    _ inR outR lo _ f g hio hin hout (by omega) hclr
    (computes_mono_hi p base _ inR lo (lo + 1) hiG _ g (by omega) (by omega) hembG) ?_
  exact computes_mono_hi p (base + fragG.length) _ lo outR (lo + 1) hiF _ f
    (by omega) (by omega) hembF

/-- The successor: copy the input across without destroying it, then raise
    the output once. The copy needs one scratch register to pour back from,
    which is `lo`, the bottom of the region the contract already guarantees
    is clear. -/
theorem builds_succ : Builds Nat.succ := by
  intro inR outR lo hio hin hout base
  refine ⟨lo + 1, [Instruction.jzdec inR (base + 3) (base + 1),
    Instruction.inc outR (base + 2), Instruction.inc lo base,
    Instruction.jzdec lo (base + 5) (base + 4), Instruction.inc inR (base + 3),
    Instruction.inc outR (base + 6)], by omega, fun p hemb s hpc hout0 hzero => ?_⟩
  have hg := embeddedAt_get p base _ hemb
  -- The copy-back fragment occupies the first five slots.
  rcases copyBack_effect p inR outR lo base (base + 3) (base + 5)
    (by omega) (by omega) (by omega)
    (by simpa only [Nat.add_zero] using hg 0 _ rfl)
    (hg 1 _ rfl) (hg 2 _ rfl)
    (by simpa only using hg 3 _ rfl)
    (by simpa only [Nat.add_assoc] using hg 4 _ rfl)
    s hpc (hzero lo (le_refl _) (by omega)) with
    ⟨s1, hr1, hpc1, hA1, hT1, hS1, hF1⟩
  -- One more increment turns the copy into the successor.
  have hstep : step p s1
      = some { pc := base + 6, regs := fun i => if i = outR then s1.regs outR + 1
        else s1.regs i } := by
    simp only [step, hpc1, hg 5 _ rfl, setReg]
  refine ⟨_, reaches_trans hr1 (Reaches.step _ _ _ hstep (Reaches.refl _)), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil]
  · simp only [if_pos, hT1, hout0, Nat.zero_add]
  · simp only []
    rw [if_neg (by omega : inR ≠ outR), hA1]
  · intro r hlor hrhi
    simp only []
    rw [if_neg (by omega : r ≠ outR)]
    have hrlo : r = lo := by omega
    rw [hrlo]
    exact hS1
  · intro r hro hrlohi
    simp only []
    rw [if_neg hro]
    by_cases hri : r = inR
    · rw [hri, hA1]
    · exact hF1 r hri hro (by omega)

/-- The empty fragment computes the constant zero: the calling convention
    already demands the output register start clear. -/
theorem builds_zero : Builds (fun _ => 0) := by
  intro inR outR lo _ _ _ base
  refine ⟨lo, [], le_refl _, fun p _ s hpc hout0 hzero => ⟨s, Reaches.refl _, ?_, hout0, rfl,
    hzero, fun r _ _ => rfl⟩⟩
  simp only [List.length_nil, Nat.add_zero, hpc]

end Register

end LeanBF
