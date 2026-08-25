/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing.Minsky

/-!
# Packing Equivalence Tests

Kernel re-assertions of what the packing layer delivers: the compiled program
is a two-counter machine, the two machines halt together, and the starting
counter is a concrete function of the input.
-/

namespace LeanBF.Tests

open LeanBF LeanBF.Register

/-- The compiled program names only the two counters. Without this the layer
    would produce a register machine that merely happens to use few. -/
example (p : Program) : MentionsBelow (compile p) 2 := compile_mentions p

/-- The table starts at zero and stops moving past the end of the program, so
    an out-of-range jump target lands where the program ends. -/
example (p : Program) : layout p 0 = 0 := by
  simp only [layout, List.take_zero, List.map_nil, List.sum_nil]

example (p : Program) (i : Nat) (hi : p.length ≤ i) : layout p i = layout p p.length :=
  layout_of_length_le p i hi

/-- The compiled program ends where the table does, which is how both
    machines agree about being out of bounds. -/
example (p : Program) : (compile p).length = layout p p.length := compile_length p

/-- Each block sits where the table says, which is the bridge to the block
    lemmas. -/
example (p : Program) (i : Nat) (hi : i < p.length) :
    EmbeddedAt (compile p) (layout p i) (compileInstr p i) := embeddedAt_compile p i hi

/-- The packed starting state holds the input as a power of two. -/
example (m : Nat) : (packedInit m).regs 0 = 2 ^ m := by
  simp only [packedInit, if_pos trivial]

example (m : Nat) : (packedInit m).regs 1 = 0 := by
  simp only [packedInit, if_neg (by omega : ¬ (1 : Nat) = 0)]

/-- A register machine halts exactly when its two-counter compilation does. -/
example (p : Program) (R : Nat) (hm : MentionsBelow p R) (hR : 0 < R) (m : Nat) :
    (∃ t, RunsTo (compile p) (packedInit m) t) ↔
      (∃ u, RunsTo p { pc := 0, regs := fun i => if i = 0 then m else 0 } u) :=
  compile_halts_iff p R hm hR m

/-- The translation to a Minsky machine reads the two counters off the two
    registers. -/
example (s : State) : (toMinskyState s).c1 = s.regs 0 := rfl

example (s : State) : (toMinskyState s).c2 = s.regs 1 := rfl

/-- An increment of register one becomes an increment of the second counter,
    and of any other register the first. -/
example (n : Nat) : toMinskyInstr (Instruction.inc 1 n) = Minsky.Instruction.inc2 n := by
  simp only [toMinskyInstr, if_pos]

example (n : Nat) : toMinskyInstr (Instruction.inc 0 n) = Minsky.Instruction.inc1 n := by
  simp only [toMinskyInstr, if_neg (by omega : ¬ (0 : Nat) = 1)]

/-- Translation preserves length, so addresses need no adjustment. -/
example (p : Program) : (toMinsky p).length = p.length := toMinsky_length p

/-- And the two machines halt together. -/
example (p : Program) (hm : MentionsBelow p 2) (s : State) :
    (∃ u, Minsky.RunsTo (toMinsky p) (toMinskyState s) u) ↔ (∃ v, RunsTo p s v) :=
  runsTo_toMinsky_iff p hm s

end LeanBF.Tests
