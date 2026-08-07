/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.Basics
import LeanBF.Theory.Simulate.CompileInstr
import LeanBF.Theory.Simulate.CompileInstrJzdec1
import LeanBF.Theory.Simulate.CompileInstrJzdec2
import LeanBF.Theory.Simulate.JzdecThenElse
import LeanBF.Theory.Simulate.WindowMatch

/-!
# Skipped and Non-Matching Windows

A window whose `pc` cell is non-zero decrements the `pc`, and
`windowBlockStart` prepares the window cells.

## Theorems

* `runsTo_window_skip`: A window whose pc cell is non-zero decrements the pc.
* `windowBlockStart_tape`: The prepared window state's cells.
-/

namespace LeanBF

/-- A window whose `pc` cell is non-zero decrements it and does nothing else. -/
theorem runsTo_window_skip (block : Program) (ms : Minsky.State) (s : State)
    (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) (hpc : ms.pc ≠ 0) :
    ∃ s', RunsTo (Compiler.window block, s) s' ∧
      s'.ptr = 4 ∧ s'.tape 1 = ms.pc - 1 ∧ s'.tape 2 = ms.c1 ∧
        s'.tape 3 = ms.c2 ∧ s'.tape 4 = 0 ∧ s'.tape 0 = 1 ∧
        s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧ s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  rcases hsim with ⟨hsptr, hspc, hsc1, hsc2, hsrunning⟩
  let hd0 : State := { thenBodyState 4 5 6 7 8 s with ptr := 1 }
  have hd0ptr : hd0.ptr = 1 := by simp only [hd0]
  have hd0pc : hd0.tape 1 = ms.pc := by
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (1 : Int) = 4)]
    rw [if_neg (by decide : ¬ (1 : Int) = 5)]
    rw [if_neg (by decide : ¬ (1 : Int) = 6)]
    rw [if_neg (by decide : ¬ (1 : Int) = 7)]
    rw [if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hspc
  have hw : ms.pc = (ms.pc - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpc))]
  let w : Nat := ms.pc - 1
  let s_else : State :=
    { elseBodyState 1 9 10 11 12 ms.pc hd0 with
      tape := fun i =>
        if i = (1 : Int) then (elseBodyState 1 9 10 11 12 ms.pc hd0).tape 1 - 1 else
        (elseBodyState 1 9 10 11 12 ms.pc hd0).tape i }
  have helse : RunsTo ([.dec_val], elseBodyState 1 9 10 11 12 ms.pc hd0) s_else := by
    have hdec : RunsTo ([.dec_val], elseBodyState 1 9 10 11 12 ms.pc hd0)
        { elseBodyState 1 9 10 11 12 ms.pc hd0 with tape := fun i =>
          if i = (1 : Int) then (elseBodyState 1 9 10 11 12 ms.pc hd0).tape 1 - 1 else
          (elseBodyState 1 9 10 11 12 ms.pc hd0).tape i } :=
      runsTo_dec_val (elseBodyState 1 9 10 11 12 ms.pc hd0)
    simpa only [s_else] using hdec
  have h1e : s_else.ptr = 1 := by simp only [s_else, elseBodyState]
  have h2e : s_else.tape 9 = 0 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (9 : Int) = 1)]
    rw [if_neg (by decide : ¬ (9 : Int) = 1)]
    rw [if_true]
  have h3e : s_else.tape 11 = 0 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (11 : Int) = 1)]
    rw [if_neg (by decide : ¬ (11 : Int) = 1)]
    rw [if_neg (by decide : ¬ (11 : Int) = 9)]
    rw [if_neg (by decide : ¬ (11 : Int) = 10)]
    rw [if_true]
  have h4e : s_else.tape 12 = 0 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (12 : Int) = 1)]
    rw [if_neg (by decide : ¬ (12 : Int) = 1)]
    rw [if_neg (by decide : ¬ (12 : Int) = 9)]
    rw [if_neg (by decide : ¬ (12 : Int) = 10)]
    rw [if_neg (by decide : ¬ (12 : Int) = 11)]
    rw [if_true]
  have hs1 : s_else.tape 1 = ms.pc - 1 := by
    simp only [s_else, elseBodyState]
    rw [if_true]
    rw [if_true]
  have hs2 : s_else.tape 2 = ms.c1 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (2 : Int) = 1)]
    rw [if_neg (by decide : ¬ (2 : Int) = 9)]
    rw [if_neg (by decide : ¬ (2 : Int) = 10)]
    rw [if_neg (by decide : ¬ (2 : Int) = 11)]
    rw [if_neg (by decide : ¬ (2 : Int) = 12)]
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (2 : Int) = 4)]
    rw [if_neg (by decide : ¬ (2 : Int) = 5)]
    rw [if_neg (by decide : ¬ (2 : Int) = 6)]
    rw [if_neg (by decide : ¬ (2 : Int) = 7)]
    rw [if_neg (by decide : ¬ (2 : Int) = 8)]
    exact hsc1
  have hs3 : s_else.tape 3 = ms.c2 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (3 : Int) = 1)]
    rw [if_neg (by decide : ¬ (3 : Int) = 9)]
    rw [if_neg (by decide : ¬ (3 : Int) = 10)]
    rw [if_neg (by decide : ¬ (3 : Int) = 11)]
    rw [if_neg (by decide : ¬ (3 : Int) = 12)]
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (3 : Int) = 4)]
    rw [if_neg (by decide : ¬ (3 : Int) = 5)]
    rw [if_neg (by decide : ¬ (3 : Int) = 6)]
    rw [if_neg (by decide : ¬ (3 : Int) = 7)]
    rw [if_neg (by decide : ¬ (3 : Int) = 8)]
    exact hsc2
  have hs4 : s_else.tape 4 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (4 : Int) = 1),
      if_neg (by decide : ¬ (4 : Int) = 9),
      if_neg (by decide : ¬ (4 : Int) = 10),
      if_neg (by decide : ¬ (4 : Int) = 11),
      if_neg (by decide : ¬ (4 : Int) = 12),
      if_true]
  have hs0 : s_else.tape 0 = 1 := by
    simp only [s_else, elseBodyState]
    rw [if_neg (by decide : ¬ (0 : Int) = 1)]
    rw [if_neg (by decide : ¬ (0 : Int) = 9)]
    rw [if_neg (by decide : ¬ (0 : Int) = 10)]
    rw [if_neg (by decide : ¬ (0 : Int) = 11)]
    rw [if_neg (by decide : ¬ (0 : Int) = 12)]
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (0 : Int) = 4)]
    rw [if_neg (by decide : ¬ (0 : Int) = 5)]
    rw [if_neg (by decide : ¬ (0 : Int) = 6)]
    rw [if_neg (by decide : ¬ (0 : Int) = 7)]
    rw [if_neg (by decide : ¬ (0 : Int) = 8)]
    exact hsrunning
  have hs5 : s_else.tape 5 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (5 : Int) = 1),
      if_neg (by decide : ¬ (5 : Int) = 9),
      if_neg (by decide : ¬ (5 : Int) = 10),
      if_neg (by decide : ¬ (5 : Int) = 11),
      if_neg (by decide : ¬ (5 : Int) = 12),
      if_neg (by decide : ¬ (5 : Int) = 4),
      if_true]
  have hs6 : s_else.tape 6 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (6 : Int) = 1),
      if_neg (by decide : ¬ (6 : Int) = 9),
      if_neg (by decide : ¬ (6 : Int) = 10),
      if_neg (by decide : ¬ (6 : Int) = 11),
      if_neg (by decide : ¬ (6 : Int) = 12),
      if_neg (by decide : ¬ (6 : Int) = 4),
      if_neg (by decide : ¬ (6 : Int) = 5),
      if_true]
  have hs8 : s_else.tape 8 = 0 := by
    simp only [s_else, elseBodyState, hd0, thenBodyState,
      if_neg (by decide : ¬ (8 : Int) = 1),
      if_neg (by decide : ¬ (8 : Int) = 9),
      if_neg (by decide : ¬ (8 : Int) = 10),
      if_neg (by decide : ¬ (8 : Int) = 11),
      if_neg (by decide : ¬ (8 : Int) = 12),
      if_neg (by decide : ¬ (8 : Int) = 4),
      if_neg (by decide : ¬ (8 : Int) = 5),
      if_neg (by decide : ¬ (8 : Int) = 6),
      if_neg (by decide : ¬ (8 : Int) = 7),
      if_true]
  have helse' : RunsTo ([.dec_val], elseBodyState 1 9 10 11 12 (w + 1) hd0) s_else := by
    rw [show ms.pc = (ms.pc - 1) + 1 from hw] at helse
    exact helse
  let innerThen : Program := Compiler.movePtr 1 4 ++ [.inc_val] ++ Compiler.movePtr 4 1 ++ block
  have hv : hd0.tape 1 = w + 1 := by
    rw [hd0pc]
    exact hw
  have hifInner : RunsTo (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val], hd0)
      (ifZeroElsePost 1 9 10 11 12 s_else) :=
    runsTo_ifZeroElse_succ w 1 9 10 11 12 innerThen [.dec_val]
      hd0 s_else hd0ptr hv
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ helse' h1e h2e h3e h4e
  let iPost : State := ifZeroElsePost 1 9 10 11 12 s_else
  have hiPtr : iPost.ptr = 1 := by rfl
  have hiPc : iPost.tape 1 = ms.pc - 1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (1 : Int) = 9), if_neg (by decide : ¬ (1 : Int) = 10),
      if_neg (by decide : ¬ (1 : Int) = 11), if_neg (by decide : ¬ (1 : Int) = 12)]
    exact hs1
  have hiC1 : iPost.tape 2 = ms.c1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (2 : Int) = 9), if_neg (by decide : ¬ (2 : Int) = 10),
      if_neg (by decide : ¬ (2 : Int) = 11), if_neg (by decide : ¬ (2 : Int) = 12)]
    exact hs2
  have hiC2 : iPost.tape 3 = ms.c2 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (3 : Int) = 9), if_neg (by decide : ¬ (3 : Int) = 10),
      if_neg (by decide : ¬ (3 : Int) = 11), if_neg (by decide : ¬ (3 : Int) = 12)]
    exact hs3
  have hiRun : iPost.tape 0 = 1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (0 : Int) = 9), if_neg (by decide : ¬ (0 : Int) = 10),
      if_neg (by decide : ¬ (0 : Int) = 11), if_neg (by decide : ¬ (0 : Int) = 12)]
    exact hs0
  have hiDone : iPost.tape 4 = 0 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (4 : Int) = 9), if_neg (by decide : ¬ (4 : Int) = 10),
      if_neg (by decide : ¬ (4 : Int) = 11), if_neg (by decide : ¬ (4 : Int) = 12)]
    exact hs4
  let s_then : State := { iPost with ptr := 4 }
  have h1 : RunsTo (Compiler.movePtr 1 4, iPost) s_then := by
    simpa only [s_then] using runsTo_movePtr 1 4 iPost hiPtr
  have hThen : RunsTo (Compiler.movePtr 4 1 ++
      Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
      Compiler.movePtr 1 4, thenBodyState 4 5 6 7 8 s) s_then :=
    RunsTo_append (Compiler.movePtr 1 4) iPost s_then
      (RunsTo_append (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val]) hd0 iPost
        (runsTo_movePtr 4 1 (thenBodyState 4 5 6 7 8 s) (by simp only [thenBodyState]))
        hifInner)
      h1
  have h1t : s_then.ptr = 4 := by simp only [s_then]
  have h2t : s_then.tape 5 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (5 : Int) = 9), if_neg (by decide : ¬ (5 : Int) = 10),
      if_neg (by decide : ¬ (5 : Int) = 11), if_neg (by decide : ¬ (5 : Int) = 12)]
    exact hs5
  have h3t : s_then.tape 6 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 9), if_neg (by decide : ¬ (6 : Int) = 10),
      if_neg (by decide : ¬ (6 : Int) = 11), if_neg (by decide : ¬ (6 : Int) = 12)]
    exact hs6
  have h4t : s_then.tape 8 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 9), if_neg (by decide : ¬ (8 : Int) = 10),
      if_neg (by decide : ¬ (8 : Int) = 11), if_neg (by decide : ¬ (8 : Int) = 12)]
    exact hs8
  have hOuter : RunsTo (Compiler.ifZeroElse 4 5 6 7 8
      (Compiler.movePtr 4 1 ++ Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
        Compiler.movePtr 1 4) [], s)
      (ifZeroElsePost 4 5 6 7 8 s_then) :=
    runsTo_ifZeroElse_zero 4 5 6 7 8
      (Compiler.movePtr 4 1 ++ Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
        Compiler.movePtr 1 4) [] s s_then hsptr hdone
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ hThen h1t h2t h3t h4t
  have hprog : Compiler.window block = Compiler.ifZeroElse 4 5 6 7 8
      (Compiler.movePtr 4 1 ++ Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++
        Compiler.movePtr 1 4) [] := by
    simp only [Compiler.window, innerThen, List.append_assoc]
  let a2 : State := ifZeroElsePost 4 5 6 7 8 s_then
  have ha2ptr : a2.ptr = 4 := by simp only [a2, ifZeroElsePost]
  have ha2tape1 : a2.tape 1 = ms.pc - 1 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (1 : Int) = 5), if_neg (by decide : ¬ (1 : Int) = 6),
      if_neg (by decide : ¬ (1 : Int) = 7), if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hiPc
  have ha2tape2 : a2.tape 2 = ms.c1 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (2 : Int) = 5), if_neg (by decide : ¬ (2 : Int) = 6),
      if_neg (by decide : ¬ (2 : Int) = 7), if_neg (by decide : ¬ (2 : Int) = 8)]
    exact hiC1
  have ha2tape3 : a2.tape 3 = ms.c2 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (3 : Int) = 5), if_neg (by decide : ¬ (3 : Int) = 6),
      if_neg (by decide : ¬ (3 : Int) = 7), if_neg (by decide : ¬ (3 : Int) = 8)]
    exact hiC2
  have ha2tape4 : a2.tape 4 = 0 := by
    simp only [a2, ifZeroElsePost]
    exact hiDone
  have ha2run : a2.tape 0 = 1 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (0 : Int) = 5), if_neg (by decide : ¬ (0 : Int) = 6),
      if_neg (by decide : ¬ (0 : Int) = 7), if_neg (by decide : ¬ (0 : Int) = 8)]
    exact hiRun
  have ha2tape5 : a2.tape 5 = 0 := by simp only [a2, ifZeroElsePost]; rw [if_true]
  have ha2tape6 : a2.tape 6 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 5), if_true]
  have ha2tape7 : a2.tape 7 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (7 : Int) = 5), if_neg (by decide : ¬ (7 : Int) = 6), if_true]
  have ha2tape8 : a2.tape 8 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 5), if_neg (by decide : ¬ (8 : Int) = 6),
      if_neg (by decide : ¬ (8 : Int) = 7), if_true]
  have hwin : RunsTo (Compiler.window block, s) a2 := by
    simpa only [hprog] using hOuter
  exact ⟨a2, hwin, ha2ptr, ha2tape1, ha2tape2, ha2tape3, ha2tape4, ha2run, ha2tape5,
    ha2tape6, ha2tape7, ha2tape8⟩

/-- The prepared window state keeps the running flag and counters, clears the
    `pc`, and sets the `done` flag and the two window flags. -/
theorem windowBlockStart_tape (s : State) :
    (windowBlockStart s).ptr = 1 ∧ (windowBlockStart s).tape 1 = 0 ∧
    (windowBlockStart s).tape 2 = s.tape 2 ∧ (windowBlockStart s).tape 3 = s.tape 3 ∧
    (windowBlockStart s).tape 0 = s.tape 0 ∧ (windowBlockStart s).tape 4 = 1 ∧
    (windowBlockStart s).tape 5 = 0 ∧ (windowBlockStart s).tape 6 = 0 ∧
    (windowBlockStart s).tape 8 = 0 ∧ (windowBlockStart s).tape 9 = 0 ∧
    (windowBlockStart s).tape 10 = 0 ∧ (windowBlockStart s).tape 12 = 0 := by
  repeat' constructor

end LeanBF
