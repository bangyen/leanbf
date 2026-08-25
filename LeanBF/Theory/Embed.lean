/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Register

/-!
# Fragment Embedding

Saying that a program contains a fragment at an address, without saying
anything about the rest of it.

Every layer that assembles a program out of pieces needs this, and it says
nothing about what the pieces compute, so it sits below all of them. The
relation is deliberately weaker than equality: it constrains only the slots
the fragment occupies, which is what lets one program host several fragments
side by side and lets each one's specification be instantiated at the same
program.

The two append lemmas are the whole point. A concatenation embedded at a base
splits into its halves embedded at that base and just past it, so a compound
fragment's proof can hand each sub-fragment exactly the hypothesis that
sub-fragment's own specification requires.

## Main definitions

* `EmbeddedAt`: A fragment occupies a program's slots at a base address.

## Theorems

* `embeddedAt_get`: Reading one slot of an embedded fragment.
* `embeddedAt_append_left`: The first half of an embedded concatenation.
* `embeddedAt_append_right`: The second half of an embedded concatenation.
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

end Register

end LeanBF
