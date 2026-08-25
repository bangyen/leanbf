/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Invariance

/-!
# Run-Level Tape Invariance Tests

Kernel re-assertions of the run-level tape invariance lemmas.
-/

namespace LeanBF.Tests

open LeanBF

example {cfg : Program × State} (s_final : State) (P : Program → State → Prop)
    (h : RunsTo cfg s_final) (hinit : P cfg.1 cfg.2)
    (hstep : ∀ {p : Program} {s : State}, P p s → ∀ {p' : Program} {s' : State},
      step p s = some (p', s') → P p' s') : P ([] : Program) s_final :=
  RunsTo_inv s_final P h hinit hstep

example (n : Int) (p : Program) (s : State) (p' : Program) (s' : State)
    (h : step p s = some (p', s')) (hptr : s.ptr < n) :
    ∀ i : Int, n ≤ i → s'.tape i = s.tape i :=
  step_preserves_tape_above n p s p' s' h hptr

example {cfg : Program × State} (s_final : State) (n : Int) (h : RunsTo cfg s_final)
    (P : Program → State → Prop) (hPinit : P cfg.1 cfg.2)
    (hPstep : ∀ {p : Program} {s : State}, P p s → ∀ {p' : Program} {s' : State},
      step p s = some (p', s') → P p' s')
    (hPptr : ∀ {p : Program} {s : State}, P p s → s.ptr < n) :
    ∀ i : Int, n ≤ i → s_final.tape i = cfg.2.tape i :=
  RunsTo_preserves_tape_above s_final n h P hPinit hPstep hPptr

example (s : State) :
    ∀ i : Int, s.ptr + 1 < i → (runSeq [.inc_val, .dec_val] s).tape i = s.tape i :=
  runSeq_incVal_decVal_preserves s

example (s : State) (hptr : s.ptr = 0) :
    ∀ i : Int, 16 < i → (runSeq (Compiler.movePtr 0 16 ++ [.inc_val]) s).tape i = s.tape i :=
  movePtr_incVal_preserves_above s hptr

/-- A pointer-bounded run preserves cells at or above the bound. -/
example (fuel : Nat) (prog : Program) (s t : State) (n : Int)
    (hb : ptrBoundedRun fuel prog s n = true) (hrun : run fuel prog s = some t) :
    ∀ i : Int, n ≤ i → t.tape i = s.tape i :=
  run_preserves_tape_above_of_ptrBounded fuel prog s t n hb hrun

/-- The check is executable: `> <` keeps the pointer below 2. -/
example : ptrBoundedRun 5 [.inc_ptr, .dec_ptr] State.mkEmpty 2 = true := by decide

/-- And it fails when the pointer escapes: `> >` reaches 2. -/
example : ptrBoundedRun 5 [.inc_ptr, .inc_ptr] State.mkEmpty 2 = false := by decide

end LeanBF.Tests
