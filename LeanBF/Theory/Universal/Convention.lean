/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Transfer
import Mathlib.Computability.PartrecCode

/-!
# Toward a Universal Register Machine

The interface a register machine fragment presents when it computes a
function, and the reduction that makes the halting question decidable at each
step bound.

A recursive function of the `Nat.Partrec.Code` kind is naturally simulated by
inducting over its structure, but `Nat.Partrec.Code.eval` need not terminate:
a diverging subcomputation inside a `comp` has to propagate outward, which the
total fragments built in `Theory.Transfer` cannot express. Mathlib's `evaln` is the step-indexed
alternative — total, computable, and primitive recursive
(`Nat.Partrec.Code.primrec_evaln`) — and `dom_iff_exists_evaln` reduces
halting to a search over it. Non-termination then lives in exactly one place,
the outer search over the step bound, rather than threaded through every
case.

The target is `Nat.Primrec f → RegComputable f`, an induction over the seven
constructors of `Nat.Primrec`. That inductive is the bare one on `ℕ → ℕ`, so
the motive stays unary and pairing is handled by machine fragments at each
node rather than by the statement. Note that `prec`'s goal mentions both
`Nat.unpaired` and `Nat.pair`, so the pairing fragments are needed inside the
induction, not only for the `left` and `right` cases.

`Computes` fixes the calling convention the seven cases share. Two parts of
it are load-bearing. The scratch region is an interval disjoint from the
named registers, so disjointness side conditions are arithmetic rather than
set reasoning. And the frame clause, saying registers outside the region and
other than the output are unchanged, is what makes sequencing provable at
all: without it nothing says the second fragment's scratch is still zero when
the first one finishes.

`computes_seq` chains two fragments through a midpoint register drawn from
the shared scratch region. That placement makes its hypotheses satisfiable
only when the first function vanishes, since the postcondition asks the
midpoint to hold an output and to be zero at once, so real composition goes
through `computes_seq_clear` in `Theory.Universal.Builder` instead. It is
kept here as the statement that isolates why the region has to be split.

## Main definitions

* `Computes`: A fragment computes a function, with a calling convention.
* `RegComputable`: A function is computed by some fragment.

## Theorems

* `dom_iff_exists_evaln`: A code halts exactly when some step bound suffices.
* `clear_reaches`: The clear loop empties a register.
* `computes_seq`: Chaining through a midpoint inside the scratch region.
-/

namespace LeanBF

/-- A code halts on an input exactly when some step bound suffices. Halting
    becomes a search over a decidable predicate, which is what lets a total
    machine express a function that need not terminate. -/
theorem dom_iff_exists_evaln (c : Nat.Partrec.Code) (n : Nat) :
    (Nat.Partrec.Code.eval c n).Dom ↔ ∃ k, (Nat.Partrec.Code.evaln k c n).isSome := by
  constructor
  · intro hd
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp (Part.get_mem hd)
    exact ⟨k, Option.isSome_of_mem hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_complete.mpr ⟨k, hx⟩⟩

namespace Register

/-- Clearing a register: the loop decrements it until it is zero. -/
theorem clear_reaches (p : Program) (r base exit : Nat)
    (h0 : p[base]? = some (Instruction.jzdec r exit base)) :
    ∀ (n : Nat) (s : State), s.pc = base → s.regs r = n →
      Reaches p s { pc := exit, regs := fun i => if i = r then 0 else s.regs i } := by
  intro n
  induction n with
  | zero =>
      intro s hpc ha
      have hstep : step p s = some { s with pc := exit } := by
        simp only [step, hpc, h0, ha, if_pos]
      have hst : ({ pc := exit, regs := s.regs } : State)
          = { pc := exit, regs := fun i => if i = r then 0 else s.regs i } := by
        congr 1
        funext i
        by_cases hir : i = r
        · rw [if_pos hir, hir, ha]
        · rw [if_neg hir]
      rw [← hst]
      exact Reaches.step s _ _ hstep (Reaches.refl _)
  | succ m ih =>
      intro s hpc ha
      have hstep : step p s
          = some { pc := base, regs := fun i => if i = r then m else s.regs i } := by
        simp only [step, hpc, h0, ha, setReg]
        rw [if_neg (by omega)]
        congr 1
      have hrec := ih { pc := base, regs := fun i => if i = r then m else s.regs i } rfl
        (by simp only [if_true])
      have hfin : ({ pc := exit, regs := fun i => if i = r then 0
            else if i = r then m else s.regs i } : State)
          = { pc := exit, regs := fun i => if i = r then 0 else s.regs i } := by
        congr 1
        funext i
        by_cases hir : i = r
        · rw [if_pos hir, if_pos hir]
        · rw [if_neg hir, if_neg hir, if_neg hir]
      rw [← hfin]
      exact Reaches.step s _ _ hstep hrec

/-- A fragment computes `f` using a scratch region `[lo, hi)`: started at
    `base` with the input in `inR`, the output register clear, and the
    scratch zeroed, it reaches `exit` with `f` of the input in `outR`, the
    input preserved, the scratch restored, and everything else untouched. -/
def Computes (p : Program) (base exit inR outR lo hi : Nat) (f : Nat → Nat) : Prop :=
  ∀ (s : State), s.pc = base → s.regs outR = 0 →
    (∀ r, lo ≤ r → r < hi → s.regs r = 0) →
    ∃ s', Reaches p s s' ∧ s'.pc = exit ∧
      s'.regs outR = f (s.regs inR) ∧ s'.regs inR = s.regs inR ∧
      (∀ r, lo ≤ r → r < hi → s'.regs r = 0) ∧
      (∀ r, r ≠ outR → (r < lo ∨ hi ≤ r) → s'.regs r = s.regs r)

theorem computes_seq (p : Program) (base mid exit inR midR outR lo hi : Nat)
    (f g : Nat → Nat)
    (hmlo : lo ≤ midR) (hmhi : midR < hi) (hmo : midR ≠ outR) (hmi : midR ≠ inR)
    (hilo : inR < lo ∨ hi ≤ inR) (holo : outR < lo ∨ hi ≤ outR) (hio : inR ≠ outR)
    (hg : Computes p base mid inR midR lo hi g)
    (hf : Computes p mid exit midR outR lo hi f) :
    Computes p base exit inR outR lo hi (f ∘ g) := by
  intro s hpc hout0 hzero
  rcases hg s hpc (hzero midR hmlo hmhi) hzero with ⟨s1, hr1, hpc1, hval1, hin1, hz1, hfr1⟩
  -- outR survives g: it is outside the scratch region and is not g's output.
  have hout1 : s1.regs outR = 0 := by
    rw [hfr1 outR (fun hc => hmo hc.symm) holo]
    exact hout0
  -- The scratch is restored, so f's precondition holds.
  rcases hf s1 hpc1 hout1 hz1 with ⟨s2, hr2, hpc2, hval2, hin2, hz2, hfr2⟩
  refine ⟨s2, reaches_trans hr1 hr2, hpc2, ?_, ?_, hz2, ?_⟩
  · rw [hval2, hval1]
    rfl
  · rw [hfr2 inR hio hilo, hin1]
  · intro r hro hlohi
    have hrm : r ≠ midR := by
      rintro rfl
      omega
    rw [hfr2 r hro hlohi, hfr1 r hrm hlohi]

/-- A function is register computable when some fragment computes it under
    the calling convention, for some choice of registers and scratch region. -/
def RegComputable (f : Nat → Nat) : Prop :=
  ∃ (p : Program) (base exit inR outR lo hi : Nat),
    inR ≠ outR ∧ (inR < lo ∨ hi ≤ inR) ∧ (outR < lo ∨ hi ≤ outR) ∧
    Computes p base exit inR outR lo hi f

end Register

end LeanBF
