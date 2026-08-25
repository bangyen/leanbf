/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Displacement.Frame

/-!
# Compiler Displacement

Frames for the compiler's own combinators, culminating in the window bound
for every compiled Minsky program: the pointer never leaves cells `0` to
`16`, so a compiled run cannot touch anything above the window.

Each combinator is framed at the cell it enters and leaves on, and the frames
chain with `fapp`. The loop bodies inside `ifZeroElse` enter at four different
scratch cells, so each is framed separately before `frame_loop` lifts it.

Where `Examples.Minsky.CountDown` proves the window bound for one program by
executing its 4245 steps, this proves it for all programs at once from the
compiler's structure, so it costs nothing per example and does not grow with
the run length.

## Theorems

* `frame_ifZeroElse`: The conditional returns to the tested cell.
* `frame_compileInstr`: A compiled instruction returns to the `pc` cell.
* `frame_window`: A dispatch window returns to the `running` cell.
* `frame_flatten`: The concatenated windows return to the `running` cell.
* `frame_compileProgram`: A compiled program returns to cell `0`.
* `compiled_preserves_above_window`: A compiled run never touches a cell
  above the window.
-/

namespace LeanBF

theorem frame_ifZeroElse (test s1 s2 s3 s4 : Nat) (thenBody elseBody : Program) (W : Int)
    (hw : (test : Int) ≤ W ∧ (s1 : Int) ≤ W ∧ (s2 : Int) ≤ W ∧ (s3 : Int) ≤ W ∧ (s4 : Int) ≤ W)
    (hthen : Frame thenBody (test : Int) (test : Int) W)
    (helse : Frame elseBody (test : Int) (test : Int) W) :
    Frame (Compiler.ifZeroElse test s1 s2 s3 s4 thenBody elseBody)
      (test : Int) (test : Int) W := by
  obtain ⟨wt, w1, w2, w3, w4⟩ := hw
  have ht : (0 : Int) ≤ (test : Int) := Int.natCast_nonneg test
  have h1 : (0 : Int) ≤ (s1 : Int) := Int.natCast_nonneg s1
  have h2 : (0 : Int) ≤ (s2 : Int) := Int.natCast_nonneg s2
  have h3 : (0 : Int) ≤ (s3 : Int) := Int.natCast_nonneg s3
  have h4 : (0 : Int) ≤ (s4 : Int) := Int.natCast_nonneg s4
  unfold Compiler.ifZeroElse
  -- Copy loop body: enters and leaves on `test`.
  have bodyCopy : Frame ([Instruction.dec_val] ++ Compiler.movePtr test s1 ++
      [Instruction.inc_val] ++ Compiler.movePtr s1 s2 ++ [Instruction.inc_val] ++
      Compiler.movePtr s2 s4 ++ [Instruction.inc_val] ++ Compiler.movePtr s4 test)
      (test : Int) (test : Int) W :=
    fapp (fapp (fapp (fapp (fapp (fapp (fapp
      (frame_still disp_dec_val _ W ht wt)
      (frame_movePtr _ _ W ht h1 wt w1))
      (frame_still disp_inc_val _ W h1 w1))
      (frame_movePtr _ _ W h1 h2 w1 w2))
      (frame_still disp_inc_val _ W h2 w2))
      (frame_movePtr _ _ W h2 h4 w2 w4))
      (frame_still disp_inc_val _ W h4 w4))
      (frame_movePtr _ _ W h4 ht w4 wt)
  -- Compare loop body: enters and leaves on `s1`.
  have bodyCmp : Frame ([Instruction.dec_val] ++ Compiler.movePtr s1 s3 ++
      [Instruction.dec_val] ++ Compiler.movePtr s3 s1) (s1 : Int) (s1 : Int) W :=
    fapp (fapp (fapp
      (frame_still disp_dec_val _ W h1 w1)
      (frame_movePtr _ _ W h1 h3 w1 w3))
      (frame_still disp_dec_val _ W h3 w3))
      (frame_movePtr _ _ W h3 h1 w3 w1)
  -- Restore loop body: enters and leaves on `s4`.
  have bodyRes : Frame ([Instruction.dec_val] ++ Compiler.movePtr s4 test ++
      [Instruction.inc_val] ++ Compiler.movePtr test s4) (s4 : Int) (s4 : Int) W :=
    fapp (fapp (fapp
      (frame_still disp_dec_val _ W h4 w4)
      (frame_movePtr _ _ W h4 ht w4 wt))
      (frame_still disp_inc_val _ W ht wt))
      (frame_movePtr _ _ W ht h4 wt w4)
  -- Else loop body: enters and leaves on `s2`.
  have bodyElse : Frame (Compiler.movePtr s2 test ++ elseBody ++
      Compiler.movePtr test s2 ++ Compiler.clearHere) (s2 : Int) (s2 : Int) W :=
    fapp (fapp (fapp
      (frame_movePtr _ _ W h2 ht w2 wt)
      helse)
      (frame_movePtr _ _ W ht h2 wt w2))
      (frame_clearHere _ W h2 w2)
  -- Then loop body: enters and leaves on `s3`.
  have bodyThen : Frame (Compiler.movePtr s3 test ++ thenBody ++
      Compiler.movePtr test s3 ++ Compiler.clearHere) (s3 : Int) (s3 : Int) W :=
    fapp (fapp (fapp
      (frame_movePtr _ _ W h3 ht w3 wt)
      hthen)
      (frame_movePtr _ _ W ht h3 wt w3))
      (frame_clearHere _ W h3 w3)
  exact fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp
    (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp (fapp
    (frame_movePtr _ _ W ht h1 wt w1)
    (frame_clearHere _ W h1 w1))
    (frame_movePtr _ _ W h1 h2 w1 w2))
    (frame_clearHere _ W h2 w2))
    (frame_movePtr _ _ W h2 h3 w2 w3))
    (frame_clearHere _ W h3 w3))
    (frame_movePtr _ _ W h3 h4 w3 w4))
    (frame_clearHere _ W h4 w4))
    (frame_movePtr _ _ W h4 ht w4 wt))
    (frame_loop _ _ W bodyCopy ht wt))
    (frame_movePtr _ _ W ht h3 wt w3))
    (frame_still disp_inc_val _ W h3 w3))
    (frame_movePtr _ _ W h3 h1 w3 w1))
    (frame_loop _ _ W bodyCmp h1 w1))
    (frame_movePtr _ _ W h1 ht w1 wt))
    (frame_movePtr _ _ W ht h4 wt w4))
    (frame_loop _ _ W bodyRes h4 w4))
    (frame_movePtr _ _ W h4 ht w4 wt))
    (frame_movePtr _ _ W ht h2 wt w2))
    (frame_loop _ _ W bodyElse h2 w2))
    (frame_movePtr _ _ W h2 ht w2 wt))
    (frame_movePtr _ _ W ht h3 wt w3))
    (frame_loop _ _ W bodyThen h3 w3))
    (frame_movePtr _ _ W h3 ht w3 wt)

theorem frame_compileInstr (instr : Minsky.Instruction) :
    Frame (Compiler.compileInstr instr) 1 1 16 := by
  have n0 : (0:Int) ≤ 0 := by decide
  have n1 : (0:Int) ≤ 1 := by decide
  have n2 : (0:Int) ≤ 2 := by decide
  have n3 : (0:Int) ≤ 3 := by decide
  have w0 : (0:Int) ≤ 16 := by decide
  have w1 : (1:Int) ≤ 16 := by decide
  have w2 : (2:Int) ≤ 16 := by decide
  have w3 : (3:Int) ≤ 16 := by decide
  cases instr with
  | inc1 next =>
      simp only [Compiler.compileInstr]
      exact fapp (fapp (fapp
        (frame_movePtr 1 2 16 n1 n2 w1 w2)
        (frame_still disp_inc_val 2 16 n2 w2))
        (frame_movePtr 2 1 16 n2 n1 w2 w1))
        (frame_setHere next 1 16 n1 w1)
  | inc2 next =>
      simp only [Compiler.compileInstr]
      exact fapp (fapp (fapp
        (frame_movePtr 1 3 16 n1 n3 w1 w3)
        (frame_still disp_inc_val 3 16 n3 w3))
        (frame_movePtr 3 1 16 n3 n1 w3 w1))
        (frame_setHere next 1 16 n1 w1)
  | halt =>
      simp only [Compiler.compileInstr]
      exact fapp (fapp
        (frame_movePtr 1 0 16 n1 n0 w1 w0)
        (frame_clearHere 0 16 n0 w0))
        (frame_movePtr 0 1 16 n0 n1 w0 w1)
  | jzdec1 z nz =>
      simp only [Compiler.compileInstr]
      refine fapp (fapp (frame_movePtr 1 2 16 n1 n2 w1 w2)
        (frame_ifZeroElse 2 13 14 15 16 _ _ 16 ⟨by decide, by decide, by decide,
          by decide, by decide⟩ ?_ ?_))
        (frame_movePtr 2 1 16 n2 n1 w2 w1)
      · exact fapp (fapp (frame_movePtr 2 1 16 n2 n1 w2 w1)
          (frame_setHere z 1 16 n1 w1)) (frame_movePtr 1 2 16 n1 n2 w1 w2)
      · exact fapp (fapp (fapp (frame_still disp_dec_val 2 16 n2 w2)
          (frame_movePtr 2 1 16 n2 n1 w2 w1))
          (frame_setHere nz 1 16 n1 w1)) (frame_movePtr 1 2 16 n1 n2 w1 w2)
  | jzdec2 z nz =>
      simp only [Compiler.compileInstr]
      refine fapp (fapp (frame_movePtr 1 3 16 n1 n3 w1 w3)
        (frame_ifZeroElse 3 13 14 15 16 _ _ 16 ⟨by decide, by decide, by decide,
          by decide, by decide⟩ ?_ ?_))
        (frame_movePtr 3 1 16 n3 n1 w3 w1)
      · exact fapp (fapp (frame_movePtr 3 1 16 n3 n1 w3 w1)
          (frame_setHere z 1 16 n1 w1)) (frame_movePtr 1 3 16 n1 n3 w1 w3)
      · exact fapp (fapp (fapp (frame_still disp_dec_val 3 16 n3 w3)
          (frame_movePtr 3 1 16 n3 n1 w3 w1))
          (frame_setHere nz 1 16 n1 w1)) (frame_movePtr 1 3 16 n1 n3 w1 w3)

theorem frame_window (block : Program) (hb : Frame block 1 1 16) :
    Frame (Compiler.window block) 4 4 16 := by
  have n1 : (0:Int) ≤ 1 := by decide
  have n4 : (0:Int) ≤ 4 := by decide
  have w1 : (1:Int) ≤ 16 := by decide
  have w4 : (4:Int) ≤ 16 := by decide
  unfold Compiler.window
  refine frame_ifZeroElse 4 5 6 7 8 _ [] 16
    ⟨by decide, by decide, by decide, by decide, by decide⟩ ?_ ?_
  · -- then: movePtr 4 1 ++ ifZeroElse 1 9 10 11 12 (...) [dec_val] ++ movePtr 1 4
    refine fapp (fapp (frame_movePtr 4 1 16 n4 n1 w4 w1)
      (frame_ifZeroElse 1 9 10 11 12 _ _ 16
        ⟨by decide, by decide, by decide, by decide, by decide⟩ ?_ ?_))
      (frame_movePtr 1 4 16 n1 n4 w1 w4)
    · exact fapp (fapp (fapp (frame_movePtr 1 4 16 n1 n4 w1 w4)
        (frame_still disp_inc_val 4 16 n4 w4))
        (frame_movePtr 4 1 16 n4 n1 w4 w1)) hb
    · exact frame_still disp_dec_val 1 16 n1 w1
  · exact ⟨0, 0, 0, by simp only [disp], by decide, by decide, by decide⟩

theorem frame_flatten (m : Minsky.Program) :
    Frame (List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr))) 4 4 16 := by
  induction m with
  | nil => exact ⟨0, 0, 0, by simp only [List.map_nil, List.flatten_nil, disp], by decide,
      by decide, by decide⟩
  | cons i rest ih =>
      simp only [List.map_cons, List.flatten_cons]
      exact fapp (frame_window _ (frame_compileInstr i)) ih

theorem frame_compileProgram (m : Minsky.Program) :
    Frame (Compiler.compileProgram m) 0 0 16 := by
  have n0 : (0:Int) ≤ 0 := by decide
  have n4 : (0:Int) ≤ 4 := by decide
  have w0 : (0:Int) ≤ 16 := by decide
  have w4 : (4:Int) ≤ 16 := by decide
  unfold Compiler.compileProgram
  refine frame_loop _ 0 16 ?_ n0 w0
  refine fapp (fapp (fapp (fapp
    (frame_movePtr 0 4 16 n0 n4 w0 w4)
    (frame_clearHere 4 16 n4 w4))
    (frame_flatten m))
    (frame_ifZeroElse 4 5 6 7 8 _ [] 16
      ⟨by decide, by decide, by decide, by decide, by decide⟩ ?_ ?_))
    (frame_movePtr 4 0 16 n4 n0 w4 w0)
  · exact fapp (fapp (frame_movePtr 4 0 16 n4 n0 w4 w0)
      (frame_clearHere 0 16 n0 w0)) (frame_movePtr 0 4 16 n0 n4 w0 w4)
  · exact ⟨0, 0, 0, by simp only [disp], by decide, by decide, by decide⟩

-- THE HEADLINE: every compiled Minsky program preserves every cell above 16.
theorem compiled_preserves_above_window (m : Minsky.Program) (s t : State)
    (hs : s.ptr = 0) (h : RunsTo (Compiler.compileProgram m, s) t) :
    ∀ i : Int, 16 < i → t.tape i = s.tape i := by
  rcases frame_compileProgram m with ⟨n, lo, hi, hd, hn, hlo, hhi⟩
  intro i hgt
  refine runsTo_disp_preserves_above _ t h n lo hi hd i ?_
  simp only [hs]
  omega

end LeanBF
