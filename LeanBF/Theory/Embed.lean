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

A fragment built by laying equal-sized pieces end to end indexes by division:
`flatMap_getElem_uniform` says the `j`-th slot of the `i`-th piece sits at
`i * w + j`, provided every piece is `w` long. Mathlib has no such lemma, and
the alternative — letting the pieces differ in size — makes each piece's
address a running total over the ones before it.

## Main definitions

* `EmbeddedAt`: A fragment occupies a program's slots at a base address.

## Theorems

* `embeddedAt_get`: Reading one slot of an embedded fragment.
* `embeddedAt_append_left`: The first half of an embedded concatenation.
* `embeddedAt_append_right`: The second half of an embedded concatenation.
* `flatMap_getElem_uniform`: Indexing a concatenation of equal-sized pieces.
* `embeddedAt_flatMap_uniform`: One piece of an embedded concatenation of
  equal-sized pieces.
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

/-- Indexing a concatenation of equal-sized pieces. When every piece is `w`
    long, the `j`-th slot of the `i`-th piece is at `i * w + j`, so an
    address splits into a piece and an offset by division. -/
theorem flatMap_getElem_uniform {α : Type*} (f : Nat → List α) (n w : Nat)
    (hw : ∀ k, k < n → (f k).length = w) (i j : Nat) (hi : i < n) (hj : j < w) :
    ((List.range n).flatMap f)[i * w + j]? = (f i)[j]? := by
  induction n generalizing i with
  | zero => omega
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hlen : ((List.range m).flatMap f).length = m * w := by
        rw [List.length_flatMap, List.map_congr_left (fun k hk =>
          hw k (by have := List.mem_range.mp hk; omega)), List.map_const',
          List.sum_replicate_nat, List.length_range]
      by_cases him : i < m
      · -- The address falls inside the pieces before the last.
        rw [List.getElem?_append_left (by
          rw [hlen]
          have hle : (i + 1) * w ≤ m * w := Nat.mul_le_mul_right w him
          have hexp : (i + 1) * w = i * w + w := Nat.succ_mul i w
          omega)]
        exact ih (fun k hk => hw k (by omega)) i him
      · -- Otherwise it is in the last piece.
        have hieq : i = m := by omega
        subst hieq
        rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
          Nat.add_sub_cancel_left]

/-- One piece of an embedded concatenation of equal-sized pieces. -/
theorem embeddedAt_flatMap_uniform (p : Program) (base : Nat) (f : Nat → Program)
    (n w : Nat) (hw : ∀ k, k < n → (f k).length = w)
    (h : EmbeddedAt p base ((List.range n).flatMap f)) (i : Nat) (hi : i < n) :
    EmbeddedAt p (base + i * w) (f i) := by
  intro j hj
  have hjw : j < w := by rw [← hw i hi]; exact hj
  have hlt : i * w + j < ((List.range n).flatMap f).length := by
    rw [List.length_flatMap, List.map_congr_left (fun k hk =>
      hw k (List.mem_range.mp hk)), List.map_const', List.sum_replicate_nat,
      List.length_range]
    have : i + 1 ≤ n := hi
    have hmul : (i + 1) * w ≤ n * w := Nat.mul_le_mul_right w this
    have hexp : (i + 1) * w = i * w + w := Nat.succ_mul i w
    omega
  rw [Nat.add_assoc, h (i * w + j) hlt, flatMap_getElem_uniform f n w hw i j hi hjw]

end Register

end LeanBF
