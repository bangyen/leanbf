/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Universal.Search

/-!
# The Universal Register Machine

Assembling the search: a single program that runs an arbitrary code on an
arbitrary input, halting exactly when that code does.

Everything the machine needs is in place. `evalnPacked_regComputable`
supplies a fragment for the step-bounded evaluator, `searchTail` decides
whether to raise the bound or stop, and `pairVar_effect` packs the bound
together with the fixed argument. What remains is to put the three in one
program and say what the whole thing does.

The layout is a loop with the head at address zero:

* `[0, 51)`: the pairing fragment, building `Nat.pair k m` in `arg`.
* `[51, 51 + n)`: the evaluator's fragment, reading `arg` into `res`.
* `[51 + n, 51 + n + 7)`: `searchTail`, which either returns to zero with
  the bound raised or halts with the answer.

Six named registers sit below the scratch region: `m` holds the packed code
and input for the whole run, `k` the current bound, `arg` the evaluator's
argument, `res` its result, `out` the answer, and `blk` a register the loop
never touches, which the tail's unconditional return jumps on.

`loopState` is the state at the top of an iteration, and the two probe
lemmas say what one pass does. Because the calling conventions all restore
what they borrow — `pairVar_effect` puts its operands back, `Computes`
restores the scratch, and the tail clears `arg` — `loopState (j + 1)` is
literally `loopState j` with the bound raised. That exactness is what lets
the two directions be short.

Forward, the bound is `Nat.find` on the predicate the evaluator decides:
below it every pass retries, and at it the tail stops. Backward is the
direction that needed the trace slice. A machine could in principle halt
somewhere other than the success branch, and no forward lemma rules that
out. `no_runsTo_of_diverges` does, without any case analysis: the step
relation is a function, so exhibiting one infinite path out of the start
state is enough to say the machine never stops, however it might otherwise
have tried to.

## Main definitions

* `headFrag`: The pairing fragment that assembles the evaluator's argument.
* `universal`: The whole program, for a given evaluator fragment.
* `loopState`: The machine at the top of an iteration.

## Theorems

* `headFrag_length`: The head occupies fifty-one slots.
* `headFrag_effect`: The head packs the bound with the run's argument.
* `universal_embeddedAt_tail`: The tail sits past the head and evaluator.
* `probe_eval`: One pass, up to the tail's test.
* `probe_retry`: A bound too small returns to the head with it raised.
* `probe_stop`: A bound that works halts with the answer.
* `probe_reaches`: Chaining retries below the first bound that works.
* `universal_halts_of_dom`: A code that halts makes the machine halt.
* `loopState_ne_succ`: Consecutive iterations differ.
* `universal_dom_of_halts`: The machine halting makes the code halt.
* `exists_evalFrag`: The evaluator's fragment, placed where U wants it.
* `universal_halts_iff`: The two directions, packaged.
* `universal_machine`: A single program whose halting decides any code's.
-/

namespace LeanBF

namespace Register

open Nat.Partrec

/-- The head of the loop: pair the current bound with the run's fixed
    argument, leaving both operands alone. Its working block is `[6, 14)`,
    which is why the scratch region starts at `6`. -/
def headFrag : Program := pairFrag 1 0 2 6 0 51

theorem headFrag_length : headFrag.length = 51 := pairFrag_length _ _ _ _ _ _

/-- The head packs the bound with the run's argument. The registers below
    the scratch other than `arg` are untouched, which is what carries the
    bound, the argument and the answer across the head each pass. -/
theorem headFrag_effect (p : Program) (hemb : EmbeddedAt p 0 headFrag) :
    ∀ (s : State), s.pc = 0 → s.regs 2 = 0 → (∀ j, j < 8 → s.regs (6 + j) = 0) →
      ∃ s', Reaches p s s' ∧ s'.pc = 51 ∧
        s'.regs 2 = Nat.pair (s.regs 1) (s.regs 0) ∧
        (∀ j, j < 8 → s'.regs (6 + j) = 0) ∧
        ∀ q, q ≠ 2 → (q < 6 ∨ 14 ≤ q) → s'.regs q = s.regs q := by
  intro s hpc hout hz
  rcases pairVar_effect p 1 0 2 6 0 51 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hemb s hpc hout hz with
    ⟨s', hr, hpc', hA, hB, hO, hZ, hFr⟩
  refine ⟨s', hr, hpc', hO, hZ, ?_⟩
  intro q hq2 hq
  by_cases hq1 : q = 1
  · rw [hq1, hA]
  · by_cases hq0 : q = 0
    · rw [hq0, hB]
    · exact hFr q hq1 hq0 hq2 hq

/-- The whole program: the head, an evaluator fragment, and the tail. The
    evaluator's fragment is a parameter because it only exists inside the
    proof of `evalnPacked_regComputable`, `Builds` being an existential. -/
def universal (ev : Program) : Program :=
  headFrag ++ ev ++ searchTail 4 1 2 3 5 0 (51 + ev.length)

/-- The machine at the top of an iteration: the head's address, the run's
    argument in `m`, the bound in `k`, and everything else clear. -/
def loopState (m j : Nat) : State :=
  { pc := 0, regs := fun i => if i = 0 then m else if i = 1 then j else 0 }

/-- One pass of the loop, up to the tail's test. The head packs the bound
    with the argument, the evaluator's fragment consumes it, and the machine
    stands at the tail with the encoded result in `res`. -/
theorem probe_eval (ev : Program) (hi : Nat) (hhi : 14 ≤ hi)
    (hev : ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked)
    (m j : Nat) :
    ∃ s', Reaches (universal ev) (loopState m j) s' ∧ s'.pc = 51 + ev.length ∧
      s'.regs 3 = evalnPacked (Nat.pair j m) ∧ s'.regs 0 = m ∧ s'.regs 1 = j ∧
      s'.regs 4 = 0 ∧ s'.regs 5 = 0 ∧ (∀ r, 6 ≤ r → r < hi → s'.regs r = 0) ∧
      ∀ r, r ≠ 2 → hi ≤ r → s'.regs r = (loopState m j).regs r := by
  set p : Program := universal ev with hp
  have hself : EmbeddedAt p 0 p := fun j _ => by rw [Nat.zero_add]
  have hsplit : EmbeddedAt p 0 (headFrag ++ ev) := by
    rw [hp, universal] at hself
    exact embeddedAt_append_left p 0 _ _ hself
  have hembH : EmbeddedAt p 0 headFrag := embeddedAt_append_left p 0 _ _ hsplit
  have hembE : EmbeddedAt p 51 ev := by
    have h := embeddedAt_append_right p 0 headFrag ev hsplit
    rwa [Nat.zero_add, headFrag_length] at h
  -- The head packs the bound with the run's argument.
  rcases headFrag_effect p hembH (loopState m j) rfl
    (by simp only [loopState]; rw [if_neg (by omega), if_neg (by omega)])
    (fun q hq => by simp only [loopState]; rw [if_neg (by omega), if_neg (by omega)]) with
    ⟨s1, hr1, hpc1, hO1, hZ1, hFr1⟩
  -- The scratch above the head's block was never touched, so it is still clear.
  have hz1 : ∀ r, 6 ≤ r → r < hi → s1.regs r = 0 := by
    intro r h6 hrhi
    by_cases hr14 : r < 14
    · have := hZ1 (r - 6) (by omega)
      rwa [show 6 + (r - 6) = r by omega] at this
    · rw [hFr1 r (by omega) (Or.inr (by omega))]
      simp only [loopState]
      rw [if_neg (by omega), if_neg (by omega)]
  rcases hev p hembE s1 hpc1
    (by rw [hFr1 3 (by omega) (Or.inl (by omega))]
        simp only [loopState]
        rw [if_neg (by omega), if_neg (by omega)]) hz1 with
    ⟨s2, hr2, hpc2, hV2, hI2, hZ2, hFr2⟩
  refine ⟨s2, reaches_trans hr1 hr2, hpc2, ?_, ?_, ?_, ?_, ?_, hZ2, ?_⟩
  · have harg : s1.regs 2 = Nat.pair j m := by
      rw [hO1]
      simp only [loopState, if_neg (by omega : (1 : Nat) ≠ 0), if_pos trivial]
    rw [hV2, harg]
  · rw [hFr2 0 (by omega) (Or.inl (by omega)), hFr1 0 (by omega) (Or.inl (by omega))]
    simp only [loopState, if_pos trivial]
  · rw [hFr2 1 (by omega) (Or.inl (by omega)), hFr1 1 (by omega) (Or.inl (by omega))]
    simp only [loopState, if_neg (by omega : (1 : Nat) ≠ 0), if_pos trivial]
  · rw [hFr2 4 (by omega) (Or.inl (by omega)), hFr1 4 (by omega) (Or.inl (by omega))]
    simp only [loopState]
    rw [if_neg (by omega), if_neg (by omega)]
  · rw [hFr2 5 (by omega) (Or.inl (by omega)), hFr1 5 (by omega) (Or.inl (by omega))]
    simp only [loopState]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro r hr2' hrhi
    rw [hFr2 r (by omega) (Or.inr hrhi), hFr1 r hr2' (Or.inr (by omega))]

/-- The tail is embedded where the head and the evaluator leave off. -/
theorem universal_embeddedAt_tail (ev : Program) :
    EmbeddedAt (universal ev) (51 + ev.length)
      (searchTail 4 1 2 3 5 0 (51 + ev.length)) := by
  have hself : EmbeddedAt (universal ev) 0 (universal ev) := fun j _ => by rw [Nat.zero_add]
  rw [universal] at hself
  have h := embeddedAt_append_right (universal ev) 0 (headFrag ++ ev) _ hself
  rwa [Nat.zero_add, List.length_append, headFrag_length] at h

/-- A bound too small: the machine returns to the head with the bound raised
    and everything else exactly as it was. The next state is `loopState`
    again, not merely something resembling it — each fragment restores what
    it borrowed, so the loop's invariant is an equality rather than a
    conjunction of clauses. -/
theorem probe_retry (ev : Program) (hi : Nat) (hhi : 14 ≤ hi)
    (hev : ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked)
    (m j : Nat) (hzero : evalnPacked (Nat.pair j m) = 0) :
    Reaches (universal ev) (loopState m j) (loopState m (j + 1)) := by
  rcases probe_eval ev hi hhi hev m j with
    ⟨s1, hr1, hpc1, hres, hm, hk, hout, hblk, hz, hFrHi⟩
  rcases searchTail_retry (universal ev) 4 1 2 3 5 0 (51 + ev.length)
    (by omega) (by omega) (by omega) (by omega)
    (universal_embeddedAt_tail ev) s1 hpc1 (by rw [hres, hzero]) hblk with
    ⟨s2, hr2, hpc2, harg2, hk2, hFr2⟩
  -- The next state is the same one, with the bound raised.
  have hs2 : s2 = loopState m (j + 1) := by
    refine State.ext hpc2 (funext fun r => ?_)
    simp only [loopState]
    by_cases hr0 : r = 0
    · rw [hr0, if_pos rfl, hFr2 0 (by omega) (by omega), hm]
    · rw [if_neg hr0]
      by_cases hr1 : r = 1
      · rw [hr1, if_pos rfl, hk2, hk]
      · rw [if_neg hr1]
        by_cases hr2 : r = 2
        · rw [hr2, harg2]
        · rw [hFr2 r hr2 hr1]
          by_cases hr3 : r = 3
          · rw [hr3, hres, hzero]
          · by_cases hr4 : r = 4
            · rw [hr4, hout]
            · by_cases hr5 : r = 5
              · rw [hr5, hblk]
              · -- Above the scratch, the loop state is zero and nothing wrote there.
                by_cases hrhi : r < hi
                · exact hz r (by omega) hrhi
                · rw [hFrHi r (by omega) (by omega)]
                  simp only [loopState]
                  rw [if_neg hr0, if_neg hr1]
  rw [← hs2]
  exact reaches_trans hr1 hr2

/-- A bound that works: the test's decrement decodes the answer, the drain
    moves it to the output, and the machine halts holding it. -/
theorem probe_stop (ev : Program) (hi : Nat) (hhi : 14 ≤ hi)
    (hev : ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked)
    (m j x : Nat) (hsucc : evalnPacked (Nat.pair j m) = x + 1) :
    ∃ t, RunsTo (universal ev) (loopState m j) t ∧ t.regs 4 = x := by
  rcases probe_eval ev hi hhi hev m j with
    ⟨s1, hr1, hpc1, hres, hm, hk, hout, hblk, hz, _⟩
  rcases searchTail_stop (universal ev) 4 1 2 3 5 0 (51 + ev.length)
    (by omega) (by omega) (by omega)
    (universal_embeddedAt_tail ev) s1 x hpc1 (by rw [hres, hsucc]) hout with
    ⟨t, hrun, _, hval⟩
  exact ⟨t, runsTo_of_reaches_runsTo _ _ _ _ hr1 hrun, hval⟩

/-- Chaining retries: if every bound below `j` fails, the machine walks from
    the first iteration to the `j`-th. -/
theorem probe_reaches (ev : Program) (hi : Nat) (hhi : 14 ≤ hi)
    (hev : ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked)
    (m j : Nat) (hfail : ∀ i, i < j → evalnPacked (Nat.pair i m) = 0) :
    Reaches (universal ev) (loopState m 0) (loopState m j) := by
  induction j with
  | zero => exact Reaches.refl _
  | succ i ih =>
      exact reaches_trans (ih fun t ht => hfail t (by omega))
        (probe_retry ev hi hhi hev m i (hfail i (by omega)))

/-- The forward direction: a code that halts on its input makes the machine
    halt. The bound is the least one the evaluator succeeds at, which exists
    because the code halts; below it every pass retries, and at it the tail
    stops. -/
theorem universal_halts_of_dom (ev : Program) (hi : Nat) (hhi : 14 ≤ hi)
    (hev : ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked)
    (c n : Nat) (hdom : (Code.eval (Denumerable.ofNat Code c) n).Dom) :
    ∃ t, RunsTo (universal ev) (loopState (Nat.pair c n) 0) t := by
  have hex : ∃ k, evalnPacked (Nat.pair k (Nat.pair c n)) ≠ 0 :=
    (evalnPacked_dom_iff c n).mp hdom
  set j : Nat := Nat.find hex with hj
  -- Every smaller bound fails, by minimality.
  have hfail : ∀ i, i < j → evalnPacked (Nat.pair i (Nat.pair c n)) = 0 := by
    intro i hi'
    by_contra hc
    have hle : Nat.find hex ≤ i := Nat.find_le hc
    rw [← hj] at hle
    omega
  -- The chosen bound succeeds, so the result is one above the answer.
  obtain ⟨x, hx⟩ : ∃ x, evalnPacked (Nat.pair j (Nat.pair c n)) = x + 1 := by
    rcases Nat.eq_zero_or_pos (evalnPacked (Nat.pair j (Nat.pair c n))) with h | h
    · exact absurd h (Nat.find_spec hex)
    · exact ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  rcases probe_stop ev hi hhi hev (Nat.pair c n) j x hx with ⟨t, hrun, _⟩
  exact ⟨t, runsTo_of_reaches_runsTo _ _ _ _
    (probe_reaches ev hi hhi hev (Nat.pair c n) j hfail) hrun⟩

/-- Consecutive iterations differ, the bound having gone up. This is what
    stops the divergence argument from being satisfied by a machine that
    stands still: each pass has to cost at least one step. -/
theorem loopState_ne_succ (m j : Nat) : loopState m j ≠ loopState m (j + 1) := by
  intro heq
  have h := congrArg (fun s => s.regs 1) heq
  simp only [loopState, if_neg (by omega : (1 : Nat) ≠ 0), if_pos trivial] at h
  omega

/-- The backward direction: the machine halting makes the code halt.

    Nothing here inspects where the machine stopped. If the code diverges,
    no bound ever succeeds, so `probe_retry` applies at every pass and the
    iterations go on forever. The step relation is a function, so that single
    infinite path is the machine's whole future: there is no other branch it
    could have taken to a halt, and `no_runsTo_of_diverges` turns the path
    into the contradiction directly. -/
theorem universal_dom_of_halts (ev : Program) (hi : Nat) (hhi : 14 ≤ hi)
    (hev : ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked)
    (c n : Nat) (hrun : ∃ u, RunsTo (universal ev) (loopState (Nat.pair c n) 0) u) :
    (Code.eval (Denumerable.ofNat Code c) n).Dom := by
  rcases hrun with ⟨u, hu⟩
  by_contra hnd
  -- No bound succeeds, so every pass retries.
  have hfail : ∀ j, evalnPacked (Nat.pair j (Nat.pair c n)) = 0 := by
    intro j
    by_contra hc
    exact hnd ((evalnPacked_dom_iff c n).mpr ⟨j, hc⟩)
  exact no_runsTo_of_diverges (universal ev) (loopState (Nat.pair c n))
    (fun j => probe_retry ev hi hhi hev _ j (hfail j))
    (fun j => loopState_ne_succ _ j) u hu

/-- The evaluator's fragment, placed where the machine wants it: at address
    fifty-one, reading `arg` into `res`, over a scratch region starting at
    six and wide enough for the head's working block.

    `evalnPacked_regComputable` cannot be used directly — `RegComputable`
    existentially binds its own base and registers, and there is no reason
    they would be these. `primrec_builds` is the right entry point, being
    parametric in exactly those choices, and `computes_mono_hi` then widens
    the region to cover the head's block. -/
theorem exists_evalFrag : ∃ (ev : Program) (hi : Nat), 14 ≤ hi ∧
    ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked := by
  rcases primrec_builds evalnPacked_primrec 2 3 6 (by omega) (by omega) (by omega) 51 with
    ⟨hi, frag, hlo, hc⟩
  refine ⟨frag, max hi 14, by omega, fun p hemb => ?_⟩
  exact computes_mono_hi p 51 _ 2 3 6 hi (max hi 14) evalnPacked
    (by omega) (by omega) (hc p hemb)

/-- The halting equivalence for one assembled machine: it halts from the
    initial state exactly when the code halts on the input. -/
theorem universal_halts_iff (ev : Program) (hi : Nat) (hhi : 14 ≤ hi)
    (hev : ∀ (p : Program), EmbeddedAt p 51 ev →
      Computes p 51 (51 + ev.length) 2 3 6 hi evalnPacked)
    (c n : Nat) :
    (∃ t, RunsTo (universal ev) (loopState (Nat.pair c n) 0) t) ↔
      (Code.eval (Denumerable.ofNat Code c) n).Dom :=
  ⟨universal_dom_of_halts ev hi hhi hev c n,
   universal_halts_of_dom ev hi hhi hev c n⟩

/-- A single register machine whose halting decides every code's halting.

    The program is fixed once and for all; only the initial state varies,
    and it varies in one register, holding the code number paired with the
    input. Halting from that state is equivalent to the code halting on the
    input, so any decision procedure for the machine's halting would decide
    `Nat.Partrec.Code`'s. -/
theorem universal_machine : ∃ (U : Program), ∀ (c n : Nat),
    (∃ t, RunsTo U (loopState (Nat.pair c n) 0) t) ↔
      (Code.eval (Denumerable.ofNat Code c) n).Dom := by
  rcases exists_evalFrag with ⟨ev, hi, hhi, hev⟩
  exact ⟨universal ev, universal_halts_iff ev hi hhi hev⟩

end Register

end LeanBF
