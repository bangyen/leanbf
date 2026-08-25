/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Displacement

/-!
# Displacement Tests

Kernel re-assertions of the syntactic pointer bounds: the composition rules,
the absent bound on unbalanced loops, and the cell-preservation conclusion.
-/

namespace LeanBF.Tests

open LeanBF

/-- Displacement bounds always bracket zero. -/
example (p : Program) (n lo hi : Int) (h : disp p = some (n, lo, hi)) :
    lo ≤ 0 ∧ 0 ≤ hi :=
  disp_brackets p n lo hi h

/-- Displacement composes across concatenation. -/
example (A B : Program) (na loa hia nb lob hib : Int)
    (hA : disp A = some (na, loa, hia)) (hB : disp B = some (nb, lob, hib)) :
    disp (A ++ B) = some (na + nb, min loa (na + lob), max hia (na + hib)) :=
  disp_append A B na loa hia nb lob hib hA hB

/-- A balanced loop keeps its body's range without repeating its motion. -/
example : disp [.loop [.inc_ptr, .dec_ptr]] = some (0, 0, 1) := by
  simp only [disp]
  norm_num

/-- An unbalanced loop has no syntactic bound: every iteration moves further. -/
example : disp [.loop [.inc_ptr]] = none := by
  simp only [disp]
  rfl

/-- `movePtr` never passes its endpoints. -/
example (i j : Int) : ∃ lo hi, disp (Compiler.movePtr i j) = some (j - i, lo, hi) ∧
    lo ≤ 0 ∧ 0 ≤ hi ∧ hi ≤ max 0 (j - i) :=
  disp_movePtr i j

/-- The payoff: a run provably never touches cells above its bound, derived
    from the program's syntax rather than by executing it. -/
example (s t : State) (h : RunsTo (Compiler.movePtr 0 5 ++ [.inc_val], s) t)
    (hs : s.ptr = 0) : ∀ i : Int, 5 < i → t.tape i = s.tape i := by
  rcases disp_movePtr 0 5 with ⟨lo, hi, hd, _, _, _⟩
  have hval : disp [Instruction.inc_val] = some (0, 0, 0) := by
    simp only [disp]
  intro i hi5
  refine runsTo_disp_preserves_above _ t h _ _ _
    (disp_append _ _ _ _ _ _ _ _ hd hval) i ?_
  simp only [hs]
  omega

end LeanBF.Tests
