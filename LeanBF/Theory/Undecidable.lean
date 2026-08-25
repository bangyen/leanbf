/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Packing
import LeanBF.Theory.Universal

/-!
# A Universal Two-Counter Machine

Joining the three reductions into one machine.

Each piece was proved on its own terms. `universal_machine` gives a register
machine whose halting is equivalent to a partial recursive code's;
`compile_halts_iff` compiles any register machine down to two counters; and
`runsTo_toMinsky_iff` reads a two-register program as a Minsky machine. This
module composes them.

The result is a single Minsky program whose halting on `(2 ^ Nat.pair c n, 0)`
is equivalent to code `c` halting on input `n`. Both the program and the
starting counters are concrete: the counters are a power of two, and the
program is fixed once and for all, only the input varying.

That is what a reduction needs. Mathlib's `ComputablePred.halting_problem`
says no computable predicate decides whether a code halts; a decision
procedure for this machine's halting would give one, since the map from `c`
and `n` to the starting counter is an ordinary computable function.

## Theorems

* `universal_minsky`: A Minsky machine whose halting decides any code's.
-/

namespace LeanBF

namespace Register

/-- A single Minsky program whose halting decides every partial recursive
    code's halting.

    The program is fixed; only the starting counter varies, and it varies as
    `2 ^ Nat.pair c n` — a computable function of the code and the input,
    which is what makes this a reduction rather than merely an
    equivalence. -/
theorem universal_minsky : ∃ (M : LeanBF.Minsky.Program), ∀ (c n : Nat),
    (∃ u, LeanBF.Minsky.RunsTo M { pc := 0, c1 := 2 ^ Nat.pair c n, c2 := 0 } u) ↔
      (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code c) n).Dom := by
  rcases universal_machine with ⟨U, hU⟩
  rcases exists_mentionsBelow U with ⟨R, hR⟩
  refine ⟨toMinsky (compile U), fun c n => ?_⟩
  -- The universal machine's start state is the packing layer's, written out.
  have hstate : ({ pc := 0, regs := fun i => if i = 0 then Nat.pair c n else 0 } : State)
      = loopState (Nat.pair c n) 0 := by
    refine State.ext rfl (funext fun q => ?_)
    simp only [loopState]
    by_cases hq : q = 0
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq]
      by_cases hq1 : q = 1
      · rw [if_pos hq1]
      · rw [if_neg hq1]
  rw [minsky_halts_iff U (max R 1) (fun i hi => by
    have := hR i hi
    cases hc : U[i] with
    | inc r next => rw [hc] at this; simp only [instrMentionsBelow] at this ⊢; omega
    | jzdec r z nz => rw [hc] at this; simp only [instrMentionsBelow] at this ⊢; omega
    | halt => simp only [instrMentionsBelow]) (by omega) (Nat.pair c n), hstate]
  exact hU c n

end Register

end LeanBF
