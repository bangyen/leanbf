/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Universal.Builder

/-!
# Fragment Builder Tests

Kernel re-assertions of the relocatable builder interface: that embeddings
split across a concatenation, that composition holds, and that the
degenerate reading of `computes_seq` is real.
-/

namespace LeanBF.Tests

open LeanBF.Register

/-- A concatenation embedded at a base embeds each half at its own base. -/
example (p : Program) (base : Nat) (A B : Program) (h : EmbeddedAt p base (A ++ B)) :
    EmbeddedAt p base A ∧ EmbeddedAt p (base + A.length) B :=
  ⟨embeddedAt_append_left p base A B h, embeddedAt_append_right p base A B h⟩

/-- A two-instruction program embeds itself at base zero. -/
example : EmbeddedAt [Instruction.inc 0 1, Instruction.halt] 0
    [Instruction.inc 0 1, Instruction.halt] := by
  intro j hj
  match j, hj with
  | 0, _ => rfl
  | 1, _ => rfl

/-- Builders compose, which is the `comp` case of the induction. -/
example (f g : Nat → Nat) (hf : Builds f) (hg : Builds g) : Builds (fun n => f (g n)) :=
  builds_comp f g hf hg

/-- The constant zero needs no instructions at all. -/
example : Builds (fun _ => 0) := builds_zero

/-- Widening the scratch region preserves what a fragment computes. -/
example (p : Program) (base exit inR outR lo hi hi' : Nat) (f : Nat → Nat)
    (hle : hi ≤ hi') (hout : outR < lo) (hc : Computes p base exit inR outR lo hi f) :
    Computes p base exit inR outR lo hi' f :=
  computes_mono_hi p base exit inR outR lo hi hi' f hle hout hc

/-- Placing the midpoint register inside the shared scratch region, as
    `computes_seq` does, forces the first function to vanish. That is why
    `computes_seq_clear` splits the region instead. -/
example (p : Program) (base mid inR midR lo hi : Nat) (g : Nat → Nat)
    (hlo : lo ≤ midR) (hhi : midR < hi)
    (hg : Computes p base mid inR midR lo hi g)
    (s : State) (hpc : s.pc = base) (h0 : s.regs midR = 0)
    (hz : ∀ r, lo ≤ r → r < hi → s.regs r = 0) : g (s.regs inR) = 0 := by
  rcases hg s hpc h0 hz with ⟨s', _, _, hval, _, hzz, _⟩
  rw [← hval]
  exact hzz midR hlo hhi

end LeanBF.Tests
