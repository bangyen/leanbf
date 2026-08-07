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

/-!
# The Matching Window

`windowBlockStart` and the window that matches the current program counter:
it runs the block and restores the pointer to the `pc` cell.

## Main definitions

* `windowBlockStart`: The state in which `block` runs inside a window.

## Theorems

* `runsTo_window_match`: A window whose pc cell is zero runs `block` and
  restores the pointer to the pc cell.
* `runsTo_dec_val`: A single `-` decrements the current cell.
-/

namespace LeanBF

/-- The state in which `block` runs inside a window: the `done` flag is set and
    the pointer is back on the `pc` cell. -/
def windowBlockStart (s : State) : State :=
  let hd0 : State := { thenBodyState 4 5 6 7 8 s with ptr := 1 }
  let sT : State := thenBodyState 1 9 10 11 12 hd0
  let m1 : State := { sT with ptr := 4 }
  let m2 : State := { m1 with tape := fun i => if i = (4 : Int) then m1.tape 4 + 1 else m1.tape i }
  { m2 with ptr := 1 }

/-- A window whose `pc` cell is zero runs `block` exactly once and sets the
    `done` flag. -/
theorem runsTo_window_match (block : Program) (ms ms' : Minsky.State) (s s'' : State)
    (running : Nat) (hsim : SimulatesAt ms 4 s) (hdone : s.tape 4 = 0) (hpc : ms.pc = 0)
    (hblock : RunsTo (block, windowBlockStart s) s'')
    (hpost : s''.ptr = 1 ∧ s''.tape 1 = ms'.pc ∧ s''.tape 2 = ms'.c1 ∧
      s''.tape 3 = ms'.c2 ∧ s''.tape 0 = running ∧ s''.tape 4 = 1 ∧
      s''.tape 5 = 0 ∧ s''.tape 6 = 0 ∧ s''.tape 8 = 0 ∧
      s''.tape 9 = 0 ∧ s''.tape 10 = 0 ∧ s''.tape 12 = 0) :
    ∃ s', RunsTo (Compiler.window block, s) s' ∧
      s'.ptr = 4 ∧ s'.tape 1 = ms'.pc ∧ s'.tape 2 = ms'.c1 ∧
        s'.tape 3 = ms'.c2 ∧ s'.tape 4 = 1 ∧ s'.tape 0 = running ∧
        s'.tape 5 = 0 ∧ s'.tape 6 = 0 ∧ s'.tape 7 = 0 ∧ s'.tape 8 = 0 := by
  rcases hsim with ⟨hsptr, hspc, hsc1, hsc2, hsrunning⟩
  rcases hpost with ⟨hpptr, hppc, hpc1, hpc2, hprun, hp4, hp5, hp6, hp8, hp9, hp10, hp12⟩
  let innerThen : Program := Compiler.movePtr 1 4 ++ [.inc_val] ++ Compiler.movePtr 4 1 ++ block
  let tb : Program := Compiler.movePtr 4 1 ++
    Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++ Compiler.movePtr 1 4
  have hsptr4 : s.ptr = 4 := hsptr
  have hspc0 : s.tape 1 = 0 := by
    rw [hspc]
    exact hpc
  let hd0 : State := { thenBodyState 4 5 6 7 8 s with ptr := 1 }
  have hd0ptr : hd0.ptr = 1 := by simp only [hd0]
  have hd0pc : hd0.tape 1 = 0 := by
    simp only [hd0, thenBodyState]
    rw [if_neg (by decide : ¬ (1 : Int) = 4), if_neg (by decide : ¬ (1 : Int) = 5),
      if_neg (by decide : ¬ (1 : Int) = 6), if_neg (by decide : ¬ (1 : Int) = 7),
      if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hspc0
  let sT : State := thenBodyState 1 9 10 11 12 hd0
  have hs1 : sT.ptr = 1 := by simp only [sT, thenBodyState]
  -- the inner then body: move to done, set it, move back, run block
  let m1 : State := { sT with ptr := 4 }
  let m2 : State := { m1 with tape := fun i => if i = (4 : Int) then 1 else m1.tape i }
  have hd0tape4 : hd0.tape 4 = 0 := by
    simp only [hd0, thenBodyState]
    rw [if_true]
  have hs4 : sT.tape 4 = 0 := by
    simp only [sT, thenBodyState]
    rw [if_neg (by decide : ¬ (4 : Int) = 1), if_neg (by decide : ¬ (4 : Int) = 9),
      if_neg (by decide : ¬ (4 : Int) = 10), if_neg (by decide : ¬ (4 : Int) = 11),
      if_neg (by decide : ¬ (4 : Int) = 12)]
    exact hd0tape4
  have hm1 : RunsTo (Compiler.movePtr 1 4, sT) m1 := by
    simpa only [m1] using runsTo_movePtr 1 4 sT hs1
  have hm2 : RunsTo ([.inc_val], m1) m2 := by
    have hinc : RunsTo ([.inc_val], m1)
        { m1 with tape := fun i => if i = m1.ptr then m1.tape m1.ptr + 1 else m1.tape i } :=
      runsTo_inc_val m1
    have heq : { m1 with tape := fun i => if i = m1.ptr then m1.tape m1.ptr + 1 else m1.tape i }
        = m2 := by
      apply State.ext
      · rfl
      · funext i
        by_cases hi : i = (4 : Int)
        · simp only [hi, if_true, m2, m1, hs4]
        · simp only [if_neg hi, m2, m1]
      · rfl
      · rfl
    rw [heq] at hinc
    exact hinc
  have hm2ptr : m2.ptr = 4 := by simp only [m2, m1]
  have hm3 : RunsTo (Compiler.movePtr 4 1, m2) (windowBlockStart s) := by
    simpa only using runsTo_movePtr 4 1 m2 hm2ptr
  have hinner : RunsTo (innerThen, sT) s'' := by
    have hc : RunsTo (Compiler.movePtr 1 4 ++ [.inc_val] ++ Compiler.movePtr 4 1 ++ block,
        sT) s'' :=
      RunsTo_append block (windowBlockStart s) s''
        (RunsTo_append (Compiler.movePtr 4 1) m2 (windowBlockStart s)
          (RunsTo_append [.inc_val] m1 m2 hm1 hm2) hm3)
        hblock
    simpa only [innerThen, List.append_assoc] using hc
  have hifInner : RunsTo (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val], hd0)
      (ifZeroElsePost 1 9 10 11 12 s'') :=
    runsTo_ifZeroElse_zero 1 9 10 11 12 innerThen [.dec_val] hd0 s'' hd0ptr hd0pc
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ hinner hpptr hp9 hp10 hp12
  let iPost : State := ifZeroElsePost 1 9 10 11 12 s''
  have hiPtr : iPost.ptr = 1 := by
    simp only [iPost, ifZeroElsePost]
  have hiPc : iPost.tape 1 = ms'.pc := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (1 : Int) = 9), if_neg (by decide : ¬ (1 : Int) = 10),
      if_neg (by decide : ¬ (1 : Int) = 11), if_neg (by decide : ¬ (1 : Int) = 12)]
    exact hppc
  have hiC1 : iPost.tape 2 = ms'.c1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (2 : Int) = 9), if_neg (by decide : ¬ (2 : Int) = 10),
      if_neg (by decide : ¬ (2 : Int) = 11), if_neg (by decide : ¬ (2 : Int) = 12)]
    exact hpc1
  have hiC2 : iPost.tape 3 = ms'.c2 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (3 : Int) = 9), if_neg (by decide : ¬ (3 : Int) = 10),
      if_neg (by decide : ¬ (3 : Int) = 11), if_neg (by decide : ¬ (3 : Int) = 12)]
    exact hpc2
  have hiRun : iPost.tape 0 = running := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (0 : Int) = 9), if_neg (by decide : ¬ (0 : Int) = 10),
      if_neg (by decide : ¬ (0 : Int) = 11), if_neg (by decide : ¬ (0 : Int) = 12)]
    exact hprun
  have hiDone : iPost.tape 4 = 1 := by
    simp only [iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (4 : Int) = 9), if_neg (by decide : ¬ (4 : Int) = 10),
      if_neg (by decide : ¬ (4 : Int) = 11), if_neg (by decide : ¬ (4 : Int) = 12)]
    exact hp4
  let s_then : State := { iPost with ptr := 4 }
  have h1 : RunsTo (Compiler.movePtr 1 4, iPost) s_then := by
    simpa only [s_then] using runsTo_movePtr 1 4 iPost hiPtr
  have hThen : RunsTo (tb, thenBodyState 4 5 6 7 8 s) s_then := by
    have hc : RunsTo (Compiler.movePtr 4 1 ++
        Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val] ++ Compiler.movePtr 1 4,
        thenBodyState 4 5 6 7 8 s) s_then :=
      RunsTo_append (Compiler.movePtr 1 4) iPost s_then
        (RunsTo_append (Compiler.ifZeroElse 1 9 10 11 12 innerThen [.dec_val]) hd0 iPost
          (runsTo_movePtr 4 1 (thenBodyState 4 5 6 7 8 s) (by simp only [thenBodyState]))
          hifInner)
        h1
    simpa only [tb, List.append_assoc] using hc
  have h1t : s_then.ptr = 4 := by simp only [s_then]
  have h2t : s_then.tape 5 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (5 : Int) = 9), if_neg (by decide : ¬ (5 : Int) = 10),
      if_neg (by decide : ¬ (5 : Int) = 11), if_neg (by decide : ¬ (5 : Int) = 12)]
    exact hp5
  have h3t : s_then.tape 6 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (6 : Int) = 9), if_neg (by decide : ¬ (6 : Int) = 10),
      if_neg (by decide : ¬ (6 : Int) = 11), if_neg (by decide : ¬ (6 : Int) = 12)]
    exact hp6
  have h4t : s_then.tape 8 = 0 := by
    simp only [s_then, iPost, ifZeroElsePost]
    rw [if_neg (by decide : ¬ (8 : Int) = 9), if_neg (by decide : ¬ (8 : Int) = 10),
      if_neg (by decide : ¬ (8 : Int) = 11), if_neg (by decide : ¬ (8 : Int) = 12)]
    exact hp8
  have hOuter : RunsTo (Compiler.ifZeroElse 4 5 6 7 8 tb [], s)
      (ifZeroElsePost 4 5 6 7 8 s_then) :=
    runsTo_ifZeroElse_zero 4 5 6 7 8 tb [] s s_then hsptr4 hdone
      ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ hThen h1t h2t h3t h4t
  have hprog : Compiler.window block = Compiler.ifZeroElse 4 5 6 7 8 tb [] := by
    simp only [Compiler.window, tb, innerThen, List.append_assoc]
  let a2 : State := ifZeroElsePost 4 5 6 7 8 s_then
  have ha2ptr : a2.ptr = 4 := by
    simp only [a2, ifZeroElsePost]
  have ha2tape1 : a2.tape 1 = ms'.pc := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (1 : Int) = 5), if_neg (by decide : ¬ (1 : Int) = 6),
      if_neg (by decide : ¬ (1 : Int) = 7), if_neg (by decide : ¬ (1 : Int) = 8)]
    exact hiPc
  have ha2tape2 : a2.tape 2 = ms'.c1 := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (2 : Int) = 5), if_neg (by decide : ¬ (2 : Int) = 6),
      if_neg (by decide : ¬ (2 : Int) = 7), if_neg (by decide : ¬ (2 : Int) = 8)]
    exact hiC1
  have ha2tape3 : a2.tape 3 = ms'.c2 := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (3 : Int) = 5), if_neg (by decide : ¬ (3 : Int) = 6),
      if_neg (by decide : ¬ (3 : Int) = 7), if_neg (by decide : ¬ (3 : Int) = 8)]
    exact hiC2
  have ha2tape4 : a2.tape 4 = 1 := by
    simp only [a2, ifZeroElsePost]
    exact hiDone
  have ha2run : a2.tape 0 = running := by
    simp only [a2, ifZeroElsePost, s_then]
    rw [if_neg (by decide : ¬ (0 : Int) = 5), if_neg (by decide : ¬ (0 : Int) = 6),
      if_neg (by decide : ¬ (0 : Int) = 7), if_neg (by decide : ¬ (0 : Int) = 8)]
    exact hiRun
  have ha2tape5 : a2.tape 5 = 0 := by
    simp only [a2, ifZeroElsePost]
    rw [if_true]
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

/-- A single `-` decrements the current cell. -/
theorem runsTo_dec_val (s : State) :
    RunsTo ([.dec_val], s)
      { s with tape := fun i => if i = s.ptr then s.tape s.ptr - 1 else s.tape i } := by
  have hstep : step [.dec_val] s = some ([], s.decVal) := by simp only [step]
  have heq : s.decVal =
      { s with tape := fun i => if i = s.ptr then s.tape s.ptr - 1 else s.tape i } := by
    apply State.ext
    · rfl
    · funext i
      by_cases hi : i = s.ptr
      · simp only [hi, if_true, State.decVal, State.modifyCell]
      · simp only [if_neg hi, State.decVal, State.modifyCell]
    · rfl
    · rfl
  rw [← heq]
  exact RunsTo.step [.dec_val] s s.decVal [] s.decVal hstep (RunsTo.halt s.decVal)

end LeanBF
