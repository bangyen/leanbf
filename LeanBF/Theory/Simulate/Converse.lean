/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Simulate.CompileLoop

/-!
# Completeness Converse

The reverse direction of the simulation: if the compiled Brainfuck program
halts, then the source Minsky machine halts. The forward direction hands the
Brainfuck run over from the Minsky run; here the Minsky run is recovered from
the Brainfuck one, by strong induction on the exact length of the halting
Brainfuck run. Each loop iteration costs at least the loop-entry step, so the
measure strictly decreases and the induction is well-founded.

## Theorems

* `runsExactly_step`: Peeling one step off an exact run shortens it by one.
* `runsExactly_append_suffix`: A run over `B ++ C` restricted to the `C`
  phase is no longer than the whole.
* `runsExactly_append_suffix_lt`: Peeling a first step makes the suffix
  strictly shorter.
* `minsky_step_isSome`: A non-terminal program counter steps.
* `minsky_halts_of_compiled_halts_aux`: The induction on the run length.
* `minsky_halts_of_compiled_halts`: A halting compiled run implies the Minsky
  machine halts.
-/

namespace LeanBF

theorem runsExactly_step (n : Nat) (prog : Program) (s t : State)
    (h : RunsExactly n prog s t) (prog' : Program) (s' : State)
    (hstep : step prog s = some (prog', s')) :
    ∃ m, RunsExactly m prog' s' t ∧ m + 1 = n := by
  cases n with
  | zero =>
      exfalso
      have := h.2
      simp only [stepsToHalt, hstep] at this
      exact Nat.succ_ne_zero 0 this
  | succ k =>
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · have := h.1
        simpa only [run, hstep] using this
      · have := h.2
        simp only [stepsToHalt, hstep, Nat.add_right_cancel_iff] at this
        exact this

-- Crux (a): if RunsTo (B, s) s1 and the whole run (B ++ C, s) is exact of
-- length n, then the suffix (C, s1) is exact of some m ≤ n, and if the
-- B-phase took at least one step then m < n.
-- Strategy: induct on the RunsTo (B,s) s1 derivation, peeling with
-- runsExactly_step and step_append.
theorem runsExactly_append_suffix (cfg : Program × State) (s1 : State)
    (hB : RunsTo cfg s1) : ∀ (C : Program) (n : Nat) (t : State),
    RunsExactly n (cfg.1 ++ C) cfg.2 t → ∃ m, RunsExactly m C s1 t ∧ m ≤ n := by
  induction hB with
  | halt s0 => intro C n t h; exact ⟨n, by simpa only [List.nil_append] using h, Nat.le_refl n⟩
  | step p s0 s2 p' s_fin hstep hrest ih =>
      intro C n t h
      have happ : step (p ++ C) s0 = some (p' ++ C, s2) := step_append p C s0 s2 p' hstep
      rcases runsExactly_step n (p ++ C) s0 t h (p' ++ C) s2 happ with ⟨k, hk, hkn⟩
      rcases ih C k t hk with ⟨m, hm, hmk⟩
      exact ⟨m, hm, by omega⟩

-- Strict version: a first step costs one, so the suffix is strictly shorter.
theorem runsExactly_append_suffix_lt (p : Program) (s0 s2 s1 : State) (p' : Program)
    (hstep : step p s0 = some (p', s2)) (hB : RunsTo (p', s2) s1)
    (C : Program) (n : Nat) (t : State)
    (h : RunsExactly n (p ++ C) s0 t) : ∃ m, RunsExactly m C s1 t ∧ m < n := by
  have happ : step (p ++ C) s0 = some (p' ++ C, s2) := step_append p C s0 s2 p' hstep
  rcases runsExactly_step n (p ++ C) s0 t h (p' ++ C) s2 happ with ⟨k, hk, hkn⟩
  rcases runsExactly_append_suffix (p', s2) s1 hB C k t hk with ⟨m, hm, hmk⟩
  exact ⟨m, hm, by omega⟩

-- A non-terminal pc means Minsky.step succeeds.
theorem minsky_step_isSome (m : Minsky.Program) (ms : Minsky.State)
    (h : ¬((m : List Minsky.Instruction)[ms.pc]? = some .halt ∨
           (m : List Minsky.Instruction)[ms.pc]? = none)) :
    ∃ ms', Minsky.step m ms = some ms' := by
  push_neg at h
  rcases h with ⟨hhalt, hnone⟩
  unfold Minsky.step
  cases hg : (m : List Minsky.Instruction)[ms.pc]? with
  | none => exact absurd hg hnone
  | some instr =>
      cases instr with
      | halt => exact absurd hg hhalt
      | inc1 n => exact ⟨_, rfl⟩
      | inc2 n => exact ⟨_, rfl⟩
      | jzdec1 z nz =>
          by_cases hc : ms.c1 = 0
          · exact ⟨_, by change (if ms.c1 = 0 then _ else _) = _; rw [if_pos hc]⟩
          · exact ⟨_, by change (if ms.c1 = 0 then _ else _) = _; rw [if_neg hc]⟩
      | jzdec2 z nz =>
          by_cases hc : ms.c2 = 0
          · exact ⟨_, by change (if ms.c2 = 0 then _ else _) = _; rw [if_pos hc]⟩
          · exact ⟨_, by change (if ms.c2 = 0 then _ else _) = _; rw [if_neg hc]⟩

-- Main converse, by strong induction on the exact BF run length.
theorem minsky_halts_of_compiled_halts_aux (m : Minsky.Program) :
    ∀ (n : Nat) (ms : Minsky.State) (s t : State),
      SimulatesAt ms 0 s →
      (s.tape 5 = 0 ∧ s.tape 6 = 0 ∧ s.tape 7 = 0 ∧ s.tape 8 = 0) →
      RunsExactly n (Compiler.compileProgram m) s t →
      ∃ ms_final, Minsky.RunsTo m ms ms_final := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ms s t hsim hclean hrun
    by_cases hterm : (m : List Minsky.Instruction)[ms.pc]? = some .halt ∨
        (m : List Minsky.Instruction)[ms.pc]? = none
    · exact ⟨ms, Minsky.RunsTo.halt ms hterm⟩
    · -- Non-terminal: the Minsky machine steps, and the BF loop peels one iteration.
      rcases minsky_step_isSome m ms hterm with ⟨ms1, hms1⟩
      rcases step_getElem m ms ms1 hms1 with ⟨instr, hget, hne, hinstr⟩
      rcases dispatchMs_step m ms instr hget hne with ⟨hd, hr, hmd⟩
      rcases runsTo_compileBody m ms s hsim (by exact hsim.2.2.2.2) hclean with ⟨s1, hb, post⟩
      -- The compiled program is a single loop over the body B.
      have hcur0 : State.currentVal s ≠ 0 := by
        simp only [State.currentVal, hsim.1, hsim.2.2.2.2]
        decide
      -- s1 simulates ms1, with the running flag restored.
      have hsim1 : SimulatesAt ms1 0 s1 := by
        change s1.ptr = 0 ∧ s1.tape 1 = ms1.pc ∧ s1.tape 2 = ms1.c1 ∧
          s1.tape 3 = ms1.c2 ∧ s1.tape 0 = 1
        refine ⟨post.1, ?_, ?_, ?_, ?_⟩
        · rw [post.2.2.1]; exact congrArg Minsky.State.pc (hmd.trans hinstr)
        · rw [post.2.2.2.1]; exact congrArg Minsky.State.c1 (hmd.trans hinstr)
        · rw [post.2.2.2.2.1]; exact congrArg Minsky.State.c2 (hmd.trans hinstr)
        · rw [post.2.1, hd, hr]; rfl
      have hclean1 : s1.tape 5 = 0 ∧ s1.tape 6 = 0 ∧ s1.tape 7 = 0 ∧ s1.tape 8 = 0 :=
        ⟨post.2.2.2.2.2.1, post.2.2.2.2.2.2.1, post.2.2.2.2.2.2.2.1, post.2.2.2.2.2.2.2.2⟩
      -- Unroll one loop iteration: compileProgram m = [loop B], and the
      -- non-zero running flag rewrites the run to B ++ [loop B].
      set B : Program := Compiler.movePtr 0 4 ++ Compiler.clearHere ++
        List.flatten (m.map (Compiler.window ∘ Compiler.compileInstr)) ++
        Compiler.ifZeroElse 4 5 6 7 8
          (Compiler.movePtr 4 0 ++ Compiler.clearHere ++ Compiler.movePtr 0 4) [] ++
        Compiler.movePtr 4 0 with hBdef
      have hB : Compiler.compileProgram m = ([.loop B] : Program) := by
        simp only [Compiler.compileProgram, hBdef]
      have hstepL : step (Compiler.compileProgram m) s = some (B ++ ([.loop B] : Program), s) := by
        rw [hB]; exact step_loop_nonzero s B hcur0
      -- Peel the loop-entry step, then the body B, leaving a shorter run.
      rcases runsExactly_step n (Compiler.compileProgram m) s t hrun
        (B ++ ([.loop B] : Program)) s hstepL with ⟨k, hk, hkn⟩
      rcases runsExactly_append_suffix (B, s) s1 hb ([.loop B] : Program) k t hk with
        ⟨j, hj, hjk⟩
      have hj' : RunsExactly j (Compiler.compileProgram m) s1 t := by rw [hB]; exact hj
      rcases ih j (by omega) ms1 s1 t hsim1 hclean1 hj' with ⟨ms_final, hrest⟩
      exact ⟨ms_final, Minsky.RunsTo.step ms ms1 ms_final hms1 hrest⟩

-- Top-level converse: a halting compiled run implies the Minsky machine halts.
theorem minsky_halts_of_compiled_halts (m : Minsky.Program) (ms : Minsky.State)
    (bfs : State) (h : RunsTo (Compiler.compileProgram m, simState ms) bfs) :
    ∃ ms_final, Minsky.RunsTo m ms ms_final := by
  rcases run_of_RunsTo (Compiler.compileProgram m, simState ms) bfs h with ⟨n, hexact⟩
  have hclean : (simState ms).tape 5 = 0 ∧ (simState ms).tape 6 = 0 ∧
      (simState ms).tape 7 = 0 ∧ (simState ms).tape 8 = 0 := by
    simp only [simState]
    repeat' constructor <;> norm_num
  exact minsky_halts_of_compiled_halts_aux m n ms (simState ms) bfs
    (simulates_simState ms) hclean hexact

end LeanBF
