/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Completeness
import LeanBF.Theory.IfZeroElse
import LeanBF.Theory.Simulate.Basics
import LeanBF.Theory.Simulate.CompileInstr
import LeanBF.Theory.Simulate.JzdecThenElse

/-!
# The Compiled `jzdec1` Block

The compiled `jzdec1` block branches on `c1`.

## Theorems

* `runsTo_compileInstr_jzdec1`: The `jzdec1` block branches on `c1`.
-/

namespace LeanBF

/-- The `jzdec1` block branches on `c1`. -/
theorem runsTo_compileInstr_jzdec1 (ifZero ifNonZero : Nat) (ms : Minsky.State) (s : State)
    (hptr : s.ptr = 1) (hc1 : s.tape 2 = ms.c1)
    (hc2 : s.tape 3 = ms.c2) (hrun : s.tape 0 = 1) :
    ∃ s', RunsTo (Compiler.compileInstr (.jzdec1 ifZero ifNonZero), s) s' ∧
      s'.ptr = 1 ∧ s'.tape 1 = (if ms.c1 = 0 then ifZero else ifNonZero) ∧
        s'.tape 2 = (if ms.c1 = 0 then ms.c1 else ms.c1 - 1) ∧
        s'.tape 3 = ms.c2 ∧ s'.tape 0 = 1 ∧
        s'.tape 4 = s.tape 4 ∧ s'.tape 5 = s.tape 5 ∧ s'.tape 6 = s.tape 6 ∧
        s'.tape 8 = s.tape 8 ∧ s'.tape 9 = s.tape 9 ∧ s'.tape 10 = s.tape 10 ∧
        s'.tape 12 = s.tape 12 := by
  let a1 : State := { s with ptr := 2 }
  have h1 : RunsTo (Compiler.movePtr 1 2, s) a1 := by
    simpa only [a1] using runsTo_movePtr 1 2 s hptr
  have ha1ptr : a1.ptr = 2 := by simp only [a1]
  have ha1tape2 : a1.tape 2 = ms.c1 := by simp only [a1, hc1]
  have ha1tape3 : a1.tape 3 = ms.c2 := by simp only [a1, hc2]
  have ha1run : a1.tape 0 = 1 := by simp only [a1, hrun]
  let thenBody : Program := Compiler.movePtr 2 1 ++ Compiler.setHere ifZero ++ Compiler.movePtr 1 2
  let elseBody : Program :=
    [.dec_val] ++ Compiler.movePtr 2 1 ++ Compiler.setHere ifNonZero ++ Compiler.movePtr 1 2
  by_cases hzero : ms.c1 = 0
  · have ht0 : a1.tape 2 = 0 := by
      rw [ha1tape2]
      exact hzero
    let s_then : State :=
      { thenBodyState 2 13 14 15 16 a1 with
        tape := fun i =>
          if i = (1 : Int) then ifZero else (thenBodyState 2 13 14 15 16 a1).tape i }
    have hthen : RunsTo (thenBody, thenBodyState 2 13 14 15 16 a1) s_then := by
      have hr : RunsTo (Compiler.movePtr 2 1 ++ Compiler.setHere ifZero ++ Compiler.movePtr 1 2,
          thenBodyState 2 13 14 15 16 a1)
          { thenBodyState 2 13 14 15 16 a1 with
            tape := fun i =>
              if i = (1 : Int) then ifZero else (thenBodyState 2 13 14 15 16 a1).tape i } :=
        runsTo_jzdecThen (2 : Int) ifZero (thenBodyState 2 13 14 15 16 a1)
          (by simp only [thenBodyState])
      simpa only [thenBody, s_then] using hr
    have h1t : s_then.ptr = 2 := by simp only [s_then, thenBodyState]
    have h2t : s_then.tape 13 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (13 : Int) = 1)]
      rw [if_neg (by decide : ¬ (13 : Int) = 2)]
      rw [if_true]
    have h3t : s_then.tape 14 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (14 : Int) = 1)]
      rw [if_neg (by decide : ¬ (14 : Int) = 2)]
      rw [if_neg (by decide : ¬ (14 : Int) = 13)]
      rw [if_true]
    have h4t : s_then.tape 16 = 0 := by
      simp only [s_then, thenBodyState]
      rw [if_neg (by decide : ¬ (16 : Int) = 1)]
      rw [if_neg (by decide : ¬ (16 : Int) = 2)]
      rw [if_neg (by decide : ¬ (16 : Int) = 13)]
      rw [if_neg (by decide : ¬ (16 : Int) = 14)]
      rw [if_neg (by decide : ¬ (16 : Int) = 15)]
      rw [if_true]
    have hif : RunsTo (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody, a1)
        (ifZeroElsePost 2 13 14 15 16 s_then) :=
      runsTo_ifZeroElse_zero 2 13 14 15 16 thenBody elseBody a1 s_then ha1ptr ht0
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ hthen h1t h2t h3t h4t
    let a2 : State := ifZeroElsePost 2 13 14 15 16 s_then
    have ha2ptr : a2.ptr = 2 := by
      simp only [a2, ifZeroElsePost]
    have ha2tape1 : a2.tape 1 = ifZero := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (1 : Int) = 13), if_neg (by decide : ¬ (1 : Int) = 14),
        if_neg (by decide : ¬ (1 : Int) = 15), if_neg (by decide : ¬ (1 : Int) = 16), if_true]
    have ha2tape2 : a2.tape 2 = ms.c1 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (2 : Int) = 13)]
      rw [if_neg (by decide : ¬ (2 : Int) = 14)]
      rw [if_neg (by decide : ¬ (2 : Int) = 15)]
      rw [if_neg (by decide : ¬ (2 : Int) = 16)]
      rw [if_neg (by decide : ¬ (2 : Int) = 1)]
      simp only [thenBodyState]
      exact hzero.symm
    have ha2tape3 : a2.tape 3 = ms.c2 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (3 : Int) = 13)]
      rw [if_neg (by decide : ¬ (3 : Int) = 14)]
      rw [if_neg (by decide : ¬ (3 : Int) = 15)]
      rw [if_neg (by decide : ¬ (3 : Int) = 16)]
      rw [if_neg (by decide : ¬ (3 : Int) = 1)]
      simp only [thenBodyState]
      exact ha1tape3
    have ha2run : a2.tape 0 = 1 := by
      simp only [a2, ifZeroElsePost, s_then]
      rw [if_neg (by decide : ¬ (0 : Int) = 13)]
      rw [if_neg (by decide : ¬ (0 : Int) = 14)]
      rw [if_neg (by decide : ¬ (0 : Int) = 15)]
      rw [if_neg (by decide : ¬ (0 : Int) = 16)]
      rw [if_neg (by decide : ¬ (0 : Int) = 1)]
      simp only [thenBodyState]
      exact ha1run
    let a3 : State := { a2 with ptr := 1 }
    have h3 : RunsTo (Compiler.movePtr 2 1, a2) a3 := by
      simpa only [a3] using runsTo_movePtr 2 1 a2 ha2ptr
    have hchain : RunsTo (Compiler.compileInstr (.jzdec1 ifZero ifNonZero), s) a3 := by
      simpa only [Compiler.compileInstr, thenBody, elseBody, List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 2 1) a2 a3
          (RunsTo_append (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody) a1 a2 h1 hif) h3)
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_true]
    · simp only [a3, ha2tape2, hzero, if_true]
    · simp only [a3, ha2tape3]
    · simp only [a3, ha2run]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (4 : Int) = 1),
        if_neg (by decide : ¬ (4 : Int) = 2),
        if_neg (by decide : ¬ (4 : Int) = 13),
        if_neg (by decide : ¬ (4 : Int) = 14),
        if_neg (by decide : ¬ (4 : Int) = 15),
        if_neg (by decide : ¬ (4 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (5 : Int) = 1),
        if_neg (by decide : ¬ (5 : Int) = 2),
        if_neg (by decide : ¬ (5 : Int) = 13),
        if_neg (by decide : ¬ (5 : Int) = 14),
        if_neg (by decide : ¬ (5 : Int) = 15),
        if_neg (by decide : ¬ (5 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (6 : Int) = 1),
        if_neg (by decide : ¬ (6 : Int) = 2),
        if_neg (by decide : ¬ (6 : Int) = 13),
        if_neg (by decide : ¬ (6 : Int) = 14),
        if_neg (by decide : ¬ (6 : Int) = 15),
        if_neg (by decide : ¬ (6 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (8 : Int) = 1),
        if_neg (by decide : ¬ (8 : Int) = 2),
        if_neg (by decide : ¬ (8 : Int) = 13),
        if_neg (by decide : ¬ (8 : Int) = 14),
        if_neg (by decide : ¬ (8 : Int) = 15),
        if_neg (by decide : ¬ (8 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (9 : Int) = 1),
        if_neg (by decide : ¬ (9 : Int) = 2),
        if_neg (by decide : ¬ (9 : Int) = 13),
        if_neg (by decide : ¬ (9 : Int) = 14),
        if_neg (by decide : ¬ (9 : Int) = 15),
        if_neg (by decide : ¬ (9 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (10 : Int) = 1),
        if_neg (by decide : ¬ (10 : Int) = 2),
        if_neg (by decide : ¬ (10 : Int) = 13),
        if_neg (by decide : ¬ (10 : Int) = 14),
        if_neg (by decide : ¬ (10 : Int) = 15),
        if_neg (by decide : ¬ (10 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_then, thenBodyState, a1,
        if_neg (by decide : ¬ (12 : Int) = 1),
        if_neg (by decide : ¬ (12 : Int) = 2),
        if_neg (by decide : ¬ (12 : Int) = 13),
        if_neg (by decide : ¬ (12 : Int) = 14),
        if_neg (by decide : ¬ (12 : Int) = 15),
        if_neg (by decide : ¬ (12 : Int) = 16)]
  · have hw : ms.c1 = (ms.c1 - 1) + 1 := by
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero))]
    let w : Nat := ms.c1 - 1
    let s_else : State :=
      { elseBodyState 2 13 14 15 16 ms.c1 a1 with
        tape := fun i =>
          if i = (2 : Int) then (elseBodyState 2 13 14 15 16 ms.c1 a1).tape 2 - 1 else
          if i = (1 : Int) then ifNonZero else (elseBodyState 2 13 14 15 16 ms.c1 a1).tape i }
    have helse : RunsTo (elseBody, elseBodyState 2 13 14 15 16 ms.c1 a1) s_else := by
      have hr : RunsTo ([.dec_val] ++ Compiler.movePtr 2 1 ++ Compiler.setHere ifNonZero ++
          Compiler.movePtr 1 2, elseBodyState 2 13 14 15 16 ms.c1 a1)
          { elseBodyState 2 13 14 15 16 ms.c1 a1 with
            tape := fun i =>
              if i = (2 : Int) then (elseBodyState 2 13 14 15 16 ms.c1 a1).tape 2 - 1 else
              if i = (1 : Int) then ifNonZero else
                (elseBodyState 2 13 14 15 16 ms.c1 a1).tape i } :=
        runsTo_jzdecElse (2 : Int) ifNonZero (elseBodyState 2 13 14 15 16 ms.c1 a1)
          (by simp only [elseBodyState]) (by decide : ¬ (2 : Int) = 1)
      simpa only [elseBody, s_else] using hr
    have h1e : s_else.ptr = 2 := by simp only [s_else, elseBodyState]
    have h2e : s_else.tape 13 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (13 : Int) = 2)]
      rw [if_neg (by decide : ¬ (13 : Int) = 1)]
      rw [if_neg (by decide : ¬ (13 : Int) = 2)]
      rw [if_true]
    have h3e : s_else.tape 15 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (15 : Int) = 2)]
      rw [if_neg (by decide : ¬ (15 : Int) = 1)]
      rw [if_neg (by decide : ¬ (15 : Int) = 13)]
      rw [if_neg (by decide : ¬ (15 : Int) = 14)]
      rw [if_neg (by decide : ¬ (15 : Int) = 2)]
      rw [if_true]
    have h4e : s_else.tape 16 = 0 := by
      simp only [s_else, elseBodyState]
      rw [if_neg (by decide : ¬ (16 : Int) = 2)]
      rw [if_neg (by decide : ¬ (16 : Int) = 1)]
      rw [if_neg (by decide : ¬ (16 : Int) = 13)]
      rw [if_neg (by decide : ¬ (16 : Int) = 14)]
      rw [if_neg (by decide : ¬ (16 : Int) = 15)]
      rw [if_neg (by decide : ¬ (16 : Int) = 2)]
      rw [if_true]
    have helse' : RunsTo (elseBody, elseBodyState 2 13 14 15 16 (w + 1) a1) s_else := by
      rw [show ms.c1 = (ms.c1 - 1) + 1 from hw] at helse
      exact helse
    have hif : RunsTo (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody, a1)
        (ifZeroElsePost 2 13 14 15 16 s_else) :=
      runsTo_ifZeroElse_succ w 2 13 14 15 16 thenBody elseBody a1 s_else ha1ptr
        (ha1tape2.trans hw)
        ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide⟩ helse' h1e h2e h3e h4e
    let a2 : State := ifZeroElsePost 2 13 14 15 16 s_else
    have ha2ptr : a2.ptr = 2 := by
      simp only [a2, ifZeroElsePost]
    have ha2tape1 : a2.tape 1 = ifNonZero := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (1 : Int) = 13)]
      rw [if_neg (by decide : ¬ (1 : Int) = 14)]
      rw [if_neg (by decide : ¬ (1 : Int) = 15)]
      rw [if_neg (by decide : ¬ (1 : Int) = 16)]
      rw [if_neg (by decide : ¬ (1 : Int) = 2)]
      rw [if_true]
    have ha2tape2 : a2.tape 2 = ms.c1 - 1 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (2 : Int) = 13)]
      rw [if_neg (by decide : ¬ (2 : Int) = 14)]
      rw [if_neg (by decide : ¬ (2 : Int) = 15)]
      rw [if_neg (by decide : ¬ (2 : Int) = 16)]
      rw [if_neg (by decide : ¬ (2 : Int) = 1)]
      rw [if_true]
      simp only [elseBodyState, if_true]
    have ha2tape3 : a2.tape 3 = ms.c2 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (3 : Int) = 13)]
      rw [if_neg (by decide : ¬ (3 : Int) = 14)]
      rw [if_neg (by decide : ¬ (3 : Int) = 15)]
      rw [if_neg (by decide : ¬ (3 : Int) = 16)]
      rw [if_neg (by decide : ¬ (3 : Int) = 1)]
      rw [if_neg (by decide : ¬ (3 : Int) = 2)]
      simp only [elseBodyState]
      exact ha1tape3
    have ha2run : a2.tape 0 = 1 := by
      simp only [a2, ifZeroElsePost, s_else]
      rw [if_neg (by decide : ¬ (0 : Int) = 13)]
      rw [if_neg (by decide : ¬ (0 : Int) = 14)]
      rw [if_neg (by decide : ¬ (0 : Int) = 15)]
      rw [if_neg (by decide : ¬ (0 : Int) = 16)]
      rw [if_neg (by decide : ¬ (0 : Int) = 1)]
      rw [if_neg (by decide : ¬ (0 : Int) = 2)]
      simp only [elseBodyState]
      exact ha1run
    let a3 : State := { a2 with ptr := 1 }
    have h3 : RunsTo (Compiler.movePtr 2 1, a2) a3 := by
      simpa only [a3] using runsTo_movePtr 2 1 a2 ha2ptr
    have hchain : RunsTo (Compiler.compileInstr (.jzdec1 ifZero ifNonZero), s) a3 := by
      simpa only [Compiler.compileInstr, thenBody, elseBody, List.append_assoc] using
        (RunsTo_append (Compiler.movePtr 2 1) a2 a3
          (RunsTo_append (Compiler.ifZeroElse 2 13 14 15 16 thenBody elseBody) a1 a2 h1 hif) h3)
    refine ⟨a3, hchain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [a3, ha2tape1, hzero, if_false]
    · simp only [a3, ha2tape2, hzero, if_false]
    · simp only [a3, ha2tape3]
    · simp only [a3, ha2run]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (4 : Int) = 1),
        if_neg (by decide : ¬ (4 : Int) = 2),
        if_neg (by decide : ¬ (4 : Int) = 13),
        if_neg (by decide : ¬ (4 : Int) = 14),
        if_neg (by decide : ¬ (4 : Int) = 15),
        if_neg (by decide : ¬ (4 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (5 : Int) = 1),
        if_neg (by decide : ¬ (5 : Int) = 2),
        if_neg (by decide : ¬ (5 : Int) = 13),
        if_neg (by decide : ¬ (5 : Int) = 14),
        if_neg (by decide : ¬ (5 : Int) = 15),
        if_neg (by decide : ¬ (5 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (6 : Int) = 1),
        if_neg (by decide : ¬ (6 : Int) = 2),
        if_neg (by decide : ¬ (6 : Int) = 13),
        if_neg (by decide : ¬ (6 : Int) = 14),
        if_neg (by decide : ¬ (6 : Int) = 15),
        if_neg (by decide : ¬ (6 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (8 : Int) = 1),
        if_neg (by decide : ¬ (8 : Int) = 2),
        if_neg (by decide : ¬ (8 : Int) = 13),
        if_neg (by decide : ¬ (8 : Int) = 14),
        if_neg (by decide : ¬ (8 : Int) = 15),
        if_neg (by decide : ¬ (8 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (9 : Int) = 1),
        if_neg (by decide : ¬ (9 : Int) = 2),
        if_neg (by decide : ¬ (9 : Int) = 13),
        if_neg (by decide : ¬ (9 : Int) = 14),
        if_neg (by decide : ¬ (9 : Int) = 15),
        if_neg (by decide : ¬ (9 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (10 : Int) = 1),
        if_neg (by decide : ¬ (10 : Int) = 2),
        if_neg (by decide : ¬ (10 : Int) = 13),
        if_neg (by decide : ¬ (10 : Int) = 14),
        if_neg (by decide : ¬ (10 : Int) = 15),
        if_neg (by decide : ¬ (10 : Int) = 16)]
    · simp only [a3, a2, ifZeroElsePost, s_else, elseBodyState, a1,
        if_neg (by decide : ¬ (12 : Int) = 1),
        if_neg (by decide : ¬ (12 : Int) = 2),
        if_neg (by decide : ¬ (12 : Int) = 13),
        if_neg (by decide : ¬ (12 : Int) = 14),
        if_neg (by decide : ¬ (12 : Int) = 15),
        if_neg (by decide : ¬ (12 : Int) = 16)]

end LeanBF
