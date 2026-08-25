/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing.Divide

/-!
# Compiling to Two Counters

Laying the blocks end to end, and saying where each one starts.

Every source instruction becomes a block, and the blocks vary in size — a
block's length depends on which register it names, through that register's
prime. `layout` is the resulting address table: the start of block `i` is the
total size of the blocks before it.

Jump targets are compiled through the same table, which is what makes an
out-of-range target behave. `layout` is defined by `List.take`, and taking
more than a list holds gives the whole list, so a target past the end of the
program maps to the end of the compiled program — out of bounds there too,
and therefore halting, which is what the source machine does at such a
counter. Nothing has to special-case it.

## Main definitions

* `blockLen`: How many slots an instruction compiles to.
* `layout`: Where a block starts.
* `compileInstr`: The block one instruction compiles to.
* `compile`: The whole compiled program.

## Theorems

* `layout_succ`: The next block starts a block later.
* `compileInstr_length`: A block's length is what the table says.
* `layout_eq_piecesBefore`: The table agrees with the concatenation's offsets.
* `embeddedAt_compile`: Each block sits where the table says.
* `compile_length`: The compiled program's length is the table's end.
* `layout_of_length_le`: Past the end, the table stops moving.
* `compile_mentions`: The compiled program names only the two counters.
-/

namespace LeanBF

namespace Register

/-- How many slots an instruction compiles to. The conditional's length
    mirrors `jzdecBlockLen`, the increment's `incBlockLen`. -/
noncomputable def blockLen : Instruction → Nat
  | .inc r _ => regPrime r + 4
  | .jzdec r _ _ => 2 + 2 * regPrime r + 2 + (regPrime r - 1) * (2 * regPrime r)
  | .halt => 1

/-- Where block `i` starts: the total size of the blocks before it. Taking
    more than the program holds gives the whole program, so a counter past
    the end maps to the end of the compiled program. -/
noncomputable def layout (p : Program) (i : Nat) : Nat :=
  ((p.take i).map blockLen).sum

theorem layout_succ (p : Program) (i : Nat) (hi : i < p.length) :
    layout p (i + 1) = layout p i + blockLen p[i] := by
  rw [layout, layout, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [List.map_append, List.sum_append_nat, Option.toList_some,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- The block one instruction compiles to, placed at its own address. -/
noncomputable def compileInstr (p : Program) (i : Nat) : Program :=
  match p[i]? with
  | none => []
  | some (.inc r next) => incBlock (regPrime r) (layout p i) (layout p next)
  | some (.jzdec r ifZero ifNonZero) =>
      jzdecBlock (regPrime r) (layout p i) (layout p ifZero) (layout p ifNonZero)
  | some .halt => [Instruction.halt]

/-- The whole compiled program. -/
noncomputable def compile (p : Program) : Program :=
  (List.range p.length).flatMap (compileInstr p)

theorem compileInstr_length (p : Program) (i : Nat) (hi : i < p.length) :
    (compileInstr p i).length = blockLen p[i] := by
  rw [compileInstr]
  split
  · next h => rw [List.getElem?_eq_getElem hi] at h; exact absurd h (by simp only [
      reduceCtorEq, not_false_eq_true])
  · next r next h =>
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h
      rw [incBlockLen, h, blockLen]
  · next r z nz h =>
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h
      rw [jzdecBlockLen, h, blockLen]
  · next h =>
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h
      rw [h, blockLen]
      simp only [List.length_cons, List.length_nil]

/-- The table agrees with where the concatenation actually puts each block.
    `layout` sums `blockLen` over the source program's prefix, while the
    concatenation offsets by the compiled blocks' own lengths; they agree
    because a block's length is what the table says it is. -/
theorem layout_eq_piecesBefore (p : Program) (i : Nat) (hi : i ≤ p.length) :
    layout p i = piecesBefore (compileInstr p) i := by
  induction i with
  | zero => simp only [layout, piecesBefore, List.take_zero, List.range_zero,
      List.map_nil, List.sum_nil]
  | succ m ih =>
      have hm : m < p.length := by omega
      rw [layout_succ p m hm, piecesBefore_succ, ih (by omega),
        compileInstr_length p m hm]

/-- Each block sits where the table says. This is the bridge from the
    compiled program's shape to the block lemmas, which speak of a fragment
    embedded at an address. -/
theorem embeddedAt_compile (p : Program) (i : Nat) (hi : i < p.length) :
    EmbeddedAt (compile p) (layout p i) (compileInstr p i) := by
  have hself : EmbeddedAt (compile p) 0 (compile p) := fun j _ => by rw [Nat.zero_add]
  rw [compile] at hself
  have h := embeddedAt_flatMap_prefix (compile p) 0 (compileInstr p) p.length hself i hi
  rwa [Nat.zero_add, ← layout_eq_piecesBefore p i (by omega)] at h

/-- The compiled program's length is where the table runs out. A source
    counter past the end therefore maps past the end of the compiled program,
    which is how the two machines agree about being out of bounds. -/
theorem compile_length (p : Program) : (compile p).length = layout p p.length := by
  rw [compile, List.length_flatMap, ← piecesBefore,
    layout_eq_piecesBefore p p.length (le_refl _)]

/-- Past the end, the table stops moving. -/
theorem layout_of_length_le (p : Program) (i : Nat) (hi : p.length ≤ i) :
    layout p i = layout p p.length := by
  simp only [layout]
  rw [List.take_of_length_le hi, List.take_of_length_le (le_refl _)]

/-- The compiled program names only the two counters. Every block does, and
    the program is nothing but blocks — which is what makes it a two-counter
    machine rather than merely a register machine that happens to use few. -/
theorem compile_mentions (p : Program) : MentionsBelow (compile p) 2 := by
  refine mentionsBelow_of_mem _ _ (fun i hi => ?_)
  rw [compile] at hi
  rcases List.mem_flatMap.mp hi with ⟨k, _, hk⟩
  -- Each block is one of the three shapes.
  rw [compileInstr] at hk
  split at hk
  · exact absurd hk List.not_mem_nil
  · exact incBlock_mentions _ _ _ i hk
  · exact jzdecBlock_mentions _ _ _ _ i hk
  · rcases List.mem_cons.mp hk with rfl | h
    · simp only [instrMentionsBelow]
    · exact absurd h List.not_mem_nil

end Register

end LeanBF
