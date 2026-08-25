/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Minsky
import LeanBF.Theory.Packing.Simulate

/-!
# From Two Registers to Two Counters

The last step down, and the shortest.

`Core.Minsky` fixes its two counters in the state structure, while a
`Register` machine names registers by number. A program that only ever names
zero and one is therefore already a Minsky machine written differently, and
the translation is syntactic: `inc 0` becomes `inc1`, `jzdec 1` becomes
`jzdec2`, and a register the program does not name cannot appear.

Nothing about the translation is a simulation in the earlier sense. The two
step relations are the same relation on different state types, so one step
matches one step and the whole argument is a pair of inductions that never
have to count. What made the packing layer hard — a source step becoming a
whole block, so that a halting run had to be recovered from a path of unknown
length — simply does not arise here.

`toMinsky` sends a register whose index is neither zero nor one to the first
counter. That case never occurs in a program `compile` produced, and pinning
it to something total is cheaper than carrying a proof obligation through
every instruction.

## Main definitions

* `toMinskyInstr`: One instruction, translated.
* `toMinsky`: A two-register program as a Minsky program.
* `toMinskyState`: A two-register state as a Minsky state.

## Theorems

* `toMinsky_length`: Translation preserves length.
* `toMinsky_getElem`: Reading a translated slot.
* `step_toMinsky`: The two step relations agree.
* `runsTo_toMinsky_iff`: The two machines halt together.
* `minsky_halts_iff`: A register machine halts exactly when the Minsky
  machine it compiles to does.
-/

namespace LeanBF

namespace Register

/-- One instruction, translated. A register other than zero or one cannot
    appear in a program the compiler produced, so it is sent to the first
    counter rather than carrying a side condition. -/
def toMinskyInstr : Instruction → LeanBF.Minsky.Instruction
  | .inc r next => if r = 1 then .inc2 next else .inc1 next
  | .jzdec r ifZero ifNonZero =>
      if r = 1 then .jzdec2 ifZero ifNonZero else .jzdec1 ifZero ifNonZero
  | .halt => .halt

/-- A two-register program as a Minsky program. -/
def toMinsky (p : Program) : LeanBF.Minsky.Program := p.map toMinskyInstr

/-- A two-register state as a Minsky state. -/
def toMinskyState (s : State) : LeanBF.Minsky.State :=
  { pc := s.pc, c1 := s.regs 0, c2 := s.regs 1 }

theorem toMinsky_length (p : Program) : (toMinsky p).length = p.length := by
  simp only [toMinsky, List.length_map]

theorem toMinsky_getElem (p : Program) (i : Nat) :
    (toMinsky p)[i]? = (p[i]?).map toMinskyInstr := by
  simp only [toMinsky, List.getElem?_map]

/-- The two step relations agree. One step matches one step, on the nose:
    the translated instruction reads the same counter and writes the same
    value, so there is nothing to count and no path to recover.

    The hypothesis is that the program names only the two counters, which is
    what makes `toMinskyState` lossless — a register the program could name
    but the Minsky state cannot hold would be dropped. -/
theorem step_toMinsky (p : Program) (hm : MentionsBelow p 2) (s : State) :
    LeanBF.Minsky.step (toMinsky p) (toMinskyState s)
      = (step p s).map toMinskyState := by
  have hpcOut : (toMinskyState s).pc = s.pc := rfl
  rcases hget : p[s.pc]? with _ | instr
  · -- Out of bounds on both sides.
    rw [LeanBF.Minsky.step, hpcOut, toMinsky_getElem, hget, step, hget]
    simp only [Option.map_none]
  have hlt : s.pc < p.length := by
    by_contra hc
    rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hc)] at hget
    exact absurd hget (by simp only [reduceCtorEq, not_false_eq_true])
  have hmi : instrMentionsBelow 2 instr := by
    have heq : p[s.pc] = instr := by
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hget
      exact hget
    rw [← heq]
    exact hm s.pc hlt
  have hpc : (toMinskyState s).pc = s.pc := rfl
  cases instr with
  | inc r next =>
      -- The register is zero or one, and each names its own counter.
      have hr : r = 0 ∨ r = 1 := by
        simp only [instrMentionsBelow] at hmi
        omega
      rw [LeanBF.Minsky.step, hpc, toMinsky_getElem, hget]
      simp only [Option.map_some, toMinskyInstr, step, hget]
      rcases hr with rfl | rfl
      · simp only [if_neg (by omega : ¬ (0 : Nat) = 1),
          toMinskyState, setReg, if_pos, if_neg (by omega : ¬ (1 : Nat) = 0)]
      · simp only [if_pos, toMinskyState, setReg, if_pos,
          if_neg (by omega : ¬ (0 : Nat) = 1)]
  | jzdec r ifZero ifNonZero =>
      have hr : r = 0 ∨ r = 1 := by
        simp only [instrMentionsBelow] at hmi
        omega
      rw [LeanBF.Minsky.step, hpc, toMinsky_getElem, hget]
      simp only [Option.map_some, toMinskyInstr]
      rcases hr with rfl | rfl
      · -- The first counter.
        by_cases hz : s.regs 0 = 0
        · have hs : step p s = some { s with pc := ifZero } := by
            simp only [step, hget, hz, if_pos]
          simp only [if_neg (by omega : ¬ (0 : Nat) = 1), toMinskyState, hz, if_pos, hs,
            Option.map_some]
        · have hs : step p s = some { setReg s 0 (s.regs 0 - 1) with pc := ifNonZero } := by
            simp only [step, hget, hz, if_false]
          simp only [if_neg (by omega : ¬ (0 : Nat) = 1), toMinskyState, hz, if_false, hs,
            Option.map_some, setReg, if_pos, if_neg (by omega : ¬ (1 : Nat) = 0)]
      · -- The second counter.
        by_cases hz : s.regs 1 = 0
        · have hs : step p s = some { s with pc := ifZero } := by
            simp only [step, hget, hz, if_pos]
          simp only [if_pos, toMinskyState, hz, if_pos, hs, Option.map_some]
        · have hs : step p s = some { setReg s 1 (s.regs 1 - 1) with pc := ifNonZero } := by
            simp only [step, hget, hz, if_false]
          simp only [if_pos, toMinskyState, hz, if_false, hs, Option.map_some, setReg,
            if_pos, if_neg (by omega : ¬ (0 : Nat) = 1)]
  | halt =>
      rw [LeanBF.Minsky.step, hpc, toMinsky_getElem, hget]
      simp only [Option.map_some, toMinskyInstr, step, hget, Option.map_none]

/-- The two machines halt together. One step matches one step, so each
    direction is an induction that rewrites the step and appeals to itself —
    no counting, and no path of unknown length to recover. -/
theorem runsTo_toMinsky_iff (p : Program) (hm : MentionsBelow p 2) (s : State) :
    (∃ u, LeanBF.Minsky.RunsTo (toMinsky p) (toMinskyState s) u) ↔
      (∃ v, RunsTo p s v) := by
  constructor
  · rintro ⟨u, hu⟩
    -- The translated run drives an induction on the register machine's side.
    generalize ht : toMinskyState s = t at hu
    induction hu generalizing s with
    | halt w hterm =>
        refine ⟨s, RunsTo.halt s ?_⟩
        rw [← ht] at hterm
        rcases hterm with hh | hn
        · -- A halt on the Minsky side came from a halt.
          left
          rw [toMinsky_getElem] at hh
          rcases hget : p[(toMinskyState s).pc]? with _ | instr
          · rw [hget] at hh
            exact absurd hh (by simp only [Option.map_none, reduceCtorEq,
              not_false_eq_true])
          · rw [hget] at hh
            simp only [Option.map_some, Option.some.injEq] at hh
            cases instr with
            | inc r next =>
                simp only [toMinskyInstr] at hh
                split at hh <;> exact absurd hh (by simp only [reduceCtorEq,
                  not_false_eq_true])
            | jzdec r z nz =>
                simp only [toMinskyInstr] at hh
                split at hh <;> exact absurd hh (by simp only [reduceCtorEq,
                  not_false_eq_true])
            | halt => exact hget
        · -- Out of bounds on the Minsky side means out of bounds here.
          right
          rw [toMinsky_getElem] at hn
          rcases hget : p[(toMinskyState s).pc]? with _ | instr
          · exact hget
          · rw [hget] at hn
            exact absurd hn (by simp only [Option.map_some, reduceCtorEq,
              not_false_eq_true])
    | step a b c hstep _ ih =>
        rw [← ht, step_toMinsky p hm s] at hstep
        rcases hsrc : step p s with _ | s'
        · rw [hsrc] at hstep
          exact absurd hstep (by simp only [Option.map_none, reduceCtorEq,
            not_false_eq_true])
        · rw [hsrc] at hstep
          simp only [Option.map_some, Option.some.injEq] at hstep
          rcases ih s' hstep with ⟨v, hv⟩
          exact ⟨v, RunsTo.step s s' v hsrc hv⟩
  · rintro ⟨v, hv⟩
    induction hv with
    | halt w hterm =>
        refine ⟨toMinskyState w, LeanBF.Minsky.RunsTo.halt _ ?_⟩
        rw [toMinsky_getElem]
        rcases hterm with hh | hn
        · left
          rw [show (toMinskyState w).pc = w.pc from rfl, hh]
          simp only [Option.map_some, toMinskyInstr]
        · right
          rw [show (toMinskyState w).pc = w.pc from rfl, hn]
          simp only [Option.map_none]
    | step a b c hstep _ ih =>
        rcases ih with ⟨u, hu⟩
        refine ⟨u, LeanBF.Minsky.RunsTo.step _ (toMinskyState b) _ ?_ hu⟩
        rw [step_toMinsky p hm a, hstep]
        simp only [Option.map_some]

/-- A register machine's Minsky image, and the counters it starts on. The
    input is packed into the first counter as `2 ^ m`. -/
theorem minsky_halts_iff (p : Program) (R : Nat) (hm : MentionsBelow p R) (hR : 0 < R)
    (m : Nat) :
    (∃ u, LeanBF.Minsky.RunsTo (toMinsky (compile p))
      { pc := 0, c1 := 2 ^ m, c2 := 0 } u) ↔
      (∃ v, RunsTo p { pc := 0, regs := fun i => if i = 0 then m else 0 } v) := by
  -- The Minsky start state is the packed one, translated.
  have hinit : toMinskyState (packedInit m) = { pc := 0, c1 := 2 ^ m, c2 := 0 } := by
    simp only [toMinskyState, packedInit, if_pos trivial,
      if_neg (by omega : ¬ (1 : Nat) = 0)]
  rw [← hinit, runsTo_toMinsky_iff (compile p) (compile_mentions p)]
  exact compile_halts_iff p R hm hR m

end Register

end LeanBF
