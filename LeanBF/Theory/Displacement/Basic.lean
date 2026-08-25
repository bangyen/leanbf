/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Invariance

/-!
# Pointer Displacement

A syntactic bound on where a program can move the pointer. `disp` reads a
program and returns `(net, lo, hi)`: the net displacement from start to
finish, and the lowest and highest offsets the pointer can reach relative to
its starting position.

The bounds are sound but not always tight, since a loop whose body never runs
still contributes its body's range. They are also incomplete: `disp` returns
`none` for a loop whose body has non-zero net displacement, because such a
loop moves the pointer further on every iteration and no syntactic bound
exists. Every loop the compiler emits is balanced, so this is not a
restriction in practice.

Where `Invariance.ptrBoundedRun` checks one concrete run by executing it,
`disp` bounds every run of a program at once, without reference to a starting
state. That is what makes it usable for a whole family of programs rather
than one example at a time.

## Main definitions

* `disp`: The syntactic displacement bounds of a program.

## Theorems

* `disp_brackets`: Displacement bounds always bracket zero.
* `disp_append`: Displacement composes across concatenation.
* `step_disp`: A step preserves the displacement bound.
* `runsTo_ptr_le`: A run keeps the pointer within the bound.
* `runsTo_disp_preserves_above`: A run preserves every cell above the bound.
* `disp_replicate_inc_ptr`: Repeated `>` moves the pointer up.
* `disp_replicate_dec_ptr`: Repeated `<` moves the pointer down.
* `disp_movePtr`: `movePtr` stays between its endpoints.
-/

namespace LeanBF

/-- The syntactic displacement bounds of a program: `(net, lo, hi)` gives the
    net pointer motion and the lowest and highest offsets reachable relative
    to the starting position. Returns `none` for a loop whose body has
    non-zero net displacement, for which no syntactic bound exists. -/
def disp : Program → Option (Int × Int × Int)
  | [] => some (0, 0, 0)
  | i :: rest =>
    match disp rest with
    | none => none
    | some (n2, lo2, hi2) =>
      match i with
      | .inc_ptr => some (n2 + 1, min 0 (1 + lo2), max 0 (1 + hi2))
      | .dec_ptr => some (n2 - 1, min 0 (-1 + lo2), max 0 (-1 + hi2))
      | .loop body =>
        match disp body with
        | none => none
        | some (nb, lob, hib) =>
          if nb = 0 then some (n2, min lob lo2, max hib hi2) else none
      | _ => some (n2, lo2, hi2)

theorem disp_brackets : ∀ (p : Program) (n lo hi : Int),
    disp p = some (n, lo, hi) → lo ≤ 0 ∧ 0 ≤ hi := by
  intro p
  induction p with
  | nil =>
      intro n lo hi h
      simp only [disp, Option.some_inj, Prod.mk.injEq] at h
      obtain ⟨_, h2, h3⟩ := h
      subst h2; subst h3
      exact ⟨le_refl 0, le_refl 0⟩
  | cons i rest ih =>
      intro n lo hi h
      rcases hr : disp rest with _ | ⟨n2, lo2, hi2⟩
      · rw [show disp (i :: rest) = none by simp only [disp, hr]] at h
        exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
      · rcases ih n2 lo2 hi2 hr with ⟨hlo2, hhi2⟩
        cases i
        case inc_ptr =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨_, h2, h3⟩ := h; subst h2; subst h3
          exact ⟨min_le_left _ _, le_max_left _ _⟩
        case dec_ptr =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨_, h2, h3⟩ := h; subst h2; subst h3
          exact ⟨min_le_left _ _, le_max_left _ _⟩
        case loop body =>
          rcases hb : disp body with _ | ⟨nb, lob, hib⟩
          · rw [show disp (Instruction.loop body :: rest) = none by
              simp only [disp, hr, hb]] at h
            exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
          · by_cases hnb : nb = 0
            · subst hnb
              simp only [disp, hr, hb, if_pos, Option.some_inj, Prod.mk.injEq] at h
              obtain ⟨_, h2, h3⟩ := h; subst h2; subst h3
              exact ⟨le_trans (min_le_right _ _) hlo2, le_trans hhi2 (le_max_right _ _)⟩
            · rw [show disp (Instruction.loop body :: rest) = none by
                simp only [disp, hr, hb, if_neg hnb]] at h
              exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
        all_goals (
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨_, h2, h3⟩ := h; subst h2; subst h3
          exact ⟨hlo2, hhi2⟩)

theorem disp_append : ∀ (A B : Program) (na loa hia nb lob hib : Int),
    disp A = some (na, loa, hia) → disp B = some (nb, lob, hib) →
    disp (A ++ B) = some (na + nb, min loa (na + lob), max hia (na + hib)) := by
  intro A
  induction A with
  | nil =>
      intro B na loa hia nb lob hib hA hB
      simp only [disp, Option.some_inj, Prod.mk.injEq] at hA
      obtain ⟨h1, h2, h3⟩ := hA
      subst h1; subst h2; subst h3
      rcases disp_brackets B nb lob hib hB with ⟨hlo, hhi⟩
      rw [List.nil_append, hB]
      simp only [Option.some_inj, Prod.mk.injEq, zero_add]
      exact ⟨trivial, (min_eq_right hlo).symm, (max_eq_right hhi).symm⟩
  | cons i rest ih =>
      intro B na loa hia nb lob hib hA hB
      rcases hr : disp rest with _ | ⟨n2, lo2, hi2⟩
      · rw [show disp (i :: rest) = none by simp only [disp, hr]] at hA
        exact absurd hA (by simp only [reduceCtorEq, not_false_eq_true])
      · have hrb := ih B n2 lo2 hi2 nb lob hib hr hB
        cases i
        case inc_ptr =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hA
          obtain ⟨e1, e2, e3⟩ := hA
          subst e1; subst e2; subst e3
          simp only [List.cons_append, disp, hrb, Option.some_inj, Prod.mk.injEq]
          refine ⟨by ring, ?_, ?_⟩
          · rw [min_assoc]; congr 1; omega
          · rw [max_assoc]; congr 1; omega
        case dec_ptr =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hA
          obtain ⟨e1, e2, e3⟩ := hA
          subst e1; subst e2; subst e3
          simp only [List.cons_append, disp, hrb, Option.some_inj, Prod.mk.injEq]
          refine ⟨by ring, ?_, ?_⟩
          · rw [min_assoc]; congr 1; omega
          · rw [max_assoc]; congr 1; omega
        case loop body =>
          rcases hb : disp body with _ | ⟨nbb, lobb, hibb⟩
          · rw [show disp (Instruction.loop body :: rest) = none by
              simp only [disp, hr, hb]] at hA
            exact absurd hA (by simp only [reduceCtorEq, not_false_eq_true])
          · by_cases hnb : nbb = 0
            · subst hnb
              simp only [disp, hr, hb, if_pos, Option.some_inj, Prod.mk.injEq] at hA
              obtain ⟨e1, e2, e3⟩ := hA
              subst e1; subst e2; subst e3
              simp only [List.cons_append, disp, hrb, hb, if_pos, Option.some_inj, Prod.mk.injEq]
              refine ⟨trivial, ?_, ?_⟩
              · rw [min_assoc]
              · rw [max_assoc]
            · rw [show disp (Instruction.loop body :: rest) = none by
                simp only [disp, hr, hb, if_neg hnb]] at hA
              exact absurd hA (by simp only [reduceCtorEq, not_false_eq_true])
        all_goals (
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hA
          obtain ⟨e1, e2, e3⟩ := hA
          subst e1; subst e2; subst e3
          simp only [List.cons_append, disp, hrb])

-- Semantic bridge: if disp p = some (n, lo, hi), then any step from s keeps
-- the successor's pointer within [s.ptr + lo, s.ptr + hi], and the remaining
-- program's disp is still defined with compatible bounds.
-- Formulate as: the INVARIANT is "∃ n lo hi, disp p = some (n,lo,hi) ∧
-- base + lo ≤ s.ptr ∧ s.ptr + hi ≤ base + HI" for a fixed base/HI.
-- Simpler: prove ptr stays ≤ base + hi where base is the START pointer.
theorem step_disp (p : Program) (s : State) (p' : Program) (s' : State)
    (h : step p s = some (p', s')) (n lo hi : Int) (hd : disp p = some (n, lo, hi)) :
    ∃ n' lo' hi', disp p' = some (n', lo', hi') ∧
      s'.ptr + hi' ≤ s.ptr + hi ∧ s.ptr + lo ≤ s'.ptr + lo' := by
  cases p with
  | nil => rw [step_empty] at h; exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | cons i rest =>
      rcases hr : disp rest with _ | ⟨n2, lo2, hi2⟩
      · rw [show disp (i :: rest) = none by simp only [disp, hr]] at hd
        exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
      · rcases disp_brackets rest n2 lo2 hi2 hr with ⟨hlo2, hhi2⟩
        cases i
        case loop body =>
          rcases hb : disp body with _ | ⟨nbb, lobb, hibb⟩
          · rw [show disp (Instruction.loop body :: rest) = none by
              simp only [disp, hr, hb]] at hd
            exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
          · by_cases hnb : nbb = 0
            · subst hnb
              simp only [disp, hr, hb, if_pos, Option.some_inj, Prod.mk.injEq] at hd
              obtain ⟨e1, e2, e3⟩ := hd
              subst e1; subst e2; subst e3
              rcases disp_brackets body 0 lobb hibb hb with ⟨hlob, hhib⟩
              by_cases hz : State.currentVal s = 0
              · -- skip: p' = rest, s' = s
                simp only [step, if_pos hz, Option.some_inj, Prod.mk.injEq] at h
                obtain ⟨hp, hs⟩ := h
                subst hp; subst hs
                exact ⟨n2, lo2, hi2, hr, by omega, by omega⟩
              · -- unroll: p' = body ++ [loop body] ++ rest
                simp only [step, if_neg hz, Option.some_inj, Prod.mk.injEq] at h
                obtain ⟨hp, hs⟩ := h
                subst hp; subst hs
                have hloop : disp (Instruction.loop body :: rest)
                    = some (n2, min lobb lo2, max hibb hi2) := by
                  simp only [disp, hr, hb, if_pos]
                have h1 : disp ([Instruction.loop body] ++ rest)
                    = some (n2, min lobb lo2, max hibb hi2) := by
                  simpa only [List.singleton_append] using hloop
                have h2 := disp_append body ([Instruction.loop body] ++ rest)
                  0 lobb hibb n2 (min lobb lo2) (max hibb hi2) hb h1
                refine ⟨0 + n2, min lobb (0 + min lobb lo2),
                  max hibb (0 + max hibb hi2), ?_, by omega, by omega⟩
                simpa only [List.append_assoc] using h2
            · rw [show disp (Instruction.loop body :: rest) = none by
                simp only [disp, hr, hb, if_neg hnb]] at hd
              exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
        case inc_ptr =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hd
          obtain ⟨e1, e2, e3⟩ := hd
          subst e1; subst e2; subst e3
          simp only [step, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hp, hs⟩ := h
          subst hp; subst hs
          refine ⟨n2, lo2, hi2, hr, ?_, ?_⟩
          · simp only [State.incPtr]; omega
          · simp only [State.incPtr]; omega
        case dec_ptr =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hd
          obtain ⟨e1, e2, e3⟩ := hd
          subst e1; subst e2; subst e3
          simp only [step, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hp, hs⟩ := h
          subst hp; subst hs
          refine ⟨n2, lo2, hi2, hr, ?_, ?_⟩
          · simp only [State.decPtr]; omega
          · simp only [State.decPtr]; omega
        case read =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hd
          obtain ⟨e1, e2, e3⟩ := hd
          subst e1; subst e2; subst e3
          rcases hin : s.input with _ | ⟨x, xs⟩ <;>
            simp only [step, hin, Option.some_inj, Prod.mk.injEq] at h <;>
            (obtain ⟨hp, hs⟩ := h; subst hp; subst hs;
             refine ⟨n2, lo2, hi2, hr, ?_, ?_⟩ <;>
               (show (_ : Int) ≤ _; simp only []; omega))
        case inc_val =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hd
          obtain ⟨e1, e2, e3⟩ := hd
          subst e1; subst e2; subst e3
          simp only [step, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hp, hs⟩ := h
          subst hp; subst hs
          refine ⟨n2, lo2, hi2, hr, ?_, ?_⟩ <;> rw [incVal_ptr]
        case dec_val =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hd
          obtain ⟨e1, e2, e3⟩ := hd
          subst e1; subst e2; subst e3
          simp only [step, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hp, hs⟩ := h
          subst hp; subst hs
          refine ⟨n2, lo2, hi2, hr, ?_, ?_⟩ <;> rw [decVal_ptr]
        case write =>
          simp only [disp, hr, Option.some_inj, Prod.mk.injEq] at hd
          obtain ⟨e1, e2, e3⟩ := hd
          subst e1; subst e2; subst e3
          simp only [step, Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨hp, hs⟩ := h
          subst hp; subst hs
          have hptr : ({ s with output := s.currentVal :: s.output } : State).ptr = s.ptr := rfl
          exact ⟨n2, lo2, hi2, hr, by rw [hptr], by rw [hptr]⟩

-- Run-level: a whole run keeps the pointer at or below the start + hi.
theorem runsTo_ptr_le (cfg : Program × State) (t : State) (h : RunsTo cfg t) :
    ∀ (n lo hi : Int), disp cfg.1 = some (n, lo, hi) →
      ∀ (bound : Int), cfg.2.ptr + hi ≤ bound → t.ptr ≤ bound := by
  induction h with
  | halt s =>
      intro n lo hi hd bound hb
      simp only [disp, Option.some_inj, Prod.mk.injEq] at hd
      obtain ⟨_, _, h3⟩ := hd
      subst h3
      simp only at hb
      omega
  | step p s s' p' sf hstep hrest ih =>
      intro n lo hi hd bound hb
      simp only at hd hb
      rcases step_disp p s p' s' hstep n lo hi hd with ⟨n', lo', hi', hd', hle, _⟩
      exact ih n' lo' hi' hd' bound (by simp only; omega)

-- The real deliverable: a run preserves every cell above start.ptr + hi.
theorem runsTo_disp_preserves_above (cfg : Program × State) (t : State) (h : RunsTo cfg t) :
    ∀ (n lo hi : Int), disp cfg.1 = some (n, lo, hi) →
      ∀ i : Int, cfg.2.ptr + hi < i → t.tape i = cfg.2.tape i := by
  induction h with
  | halt s => intro n lo hi hd i hi2; rfl
  | step p s s' p' sf hstep hrest ih =>
      intro n lo hi hd i hlt
      simp only at hd hlt ⊢
      rcases step_disp p s p' s' hstep n lo hi hd with ⟨n', lo', hi', hd', hle, _⟩
      have hbr := disp_brackets p' n' lo' hi' hd'
      have hbr0 := disp_brackets p n lo hi hd
      have hstep_pres : s'.tape i = s.tape i := by
        refine step_preserves_tape_above (s.ptr + hi + 1) p s p' s' hstep (by omega) i (by omega)
      rw [ih n' lo' hi' hd' i (by simp only; omega), hstep_pres]

theorem disp_replicate_inc_ptr : ∀ n : Nat,
    disp (List.replicate n .inc_ptr) = some ((n : Int), 0, (n : Int)) := by
  intro n
  induction n with
  | zero => simp only [List.replicate, disp, Nat.cast_zero]
  | succ k ih =>
      rw [List.replicate_succ]
      simp only [disp, ih, Option.some_inj, Prod.mk.injEq]
      refine ⟨by push_cast; ring, by omega, by push_cast; omega⟩

theorem disp_replicate_dec_ptr : ∀ n : Nat,
    disp (List.replicate n .dec_ptr) = some (-(n : Int), -(n : Int), 0) := by
  intro n
  induction n with
  | zero => simp only [List.replicate, disp, Nat.cast_zero, neg_zero]
  | succ k ih =>
      rw [List.replicate_succ]
      simp only [disp, ih, Option.some_inj, Prod.mk.injEq]
      refine ⟨by push_cast; ring, by push_cast; omega, by omega⟩

theorem disp_movePtr (i j : Int) :
    ∃ lo hi, disp (Compiler.movePtr i j) = some (j - i, lo, hi) ∧
      lo ≤ 0 ∧ 0 ≤ hi ∧ hi ≤ max 0 (j - i) := by
  unfold Compiler.movePtr
  by_cases h : i < j
  · rw [if_pos h]
    refine ⟨0, ((j - i).toNat : Int), ?_, le_refl 0, ?_, ?_⟩
    · rw [disp_replicate_inc_ptr]
      have : ((j - i).toNat : Int) = j - i := by omega
      rw [this]
    · omega
    · omega
  · rw [if_neg h]
    refine ⟨-((i - j).toNat : Int), 0, ?_, ?_, le_refl 0, ?_⟩
    · rw [disp_replicate_dec_ptr]
      have hc : ((i - j).toNat : Int) = i - j := by omega
      rw [hc]
      simp only [Option.some_inj, Prod.mk.injEq, and_true]
      omega
    · omega
    · exact le_max_left 0 (j - i)

end LeanBF
