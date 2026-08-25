/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Universal

/-!
# Universal Machine Tests

Kernel re-assertions of the halting reduction and the calling convention.
-/

namespace LeanBF.Tests

open LeanBF

/-- Halting reduces to a search over a step bound. -/
example (c : Nat.Partrec.Code) (n : Nat) :
    (Nat.Partrec.Code.eval c n).Dom ↔ ∃ k, (Nat.Partrec.Code.evaln k c n).isSome :=
  dom_iff_exists_evaln c n

/-- At each step bound the question is decidable, which is what a total
    machine can test. -/
example (k : Nat) (c : Nat.Partrec.Code) (n : Nat) :
    Decidable ((Nat.Partrec.Code.evaln k c n).isSome) :=
  inferInstance

/-- `evaln` is primitive recursive, so a machine for it follows from a
    machine for primitive recursion rather than needing its own. -/
example : Primrec fun a : (Nat × Nat.Partrec.Code) × Nat =>
    Nat.Partrec.Code.evaln a.1.1 a.1.2 a.2 :=
  Nat.Partrec.Code.primrec_evaln

/-- Fragments compose, which is the `comp` case of the induction ahead. -/
example (p : Register.Program) (base mid exit inR midR outR lo hi : Nat) (f g : Nat → Nat)
    (hmlo : lo ≤ midR) (hmhi : midR < hi) (hmo : midR ≠ outR) (hmi : midR ≠ inR)
    (hilo : inR < lo ∨ hi ≤ inR) (holo : outR < lo ∨ hi ≤ outR) (hio : inR ≠ outR)
    (hg : Register.Computes p base mid inR midR lo hi g)
    (hf : Register.Computes p mid exit midR outR lo hi f) :
    Register.Computes p base exit inR outR lo hi (f ∘ g) :=
  Register.computes_seq p base mid exit inR midR outR lo hi f g
    hmlo hmhi hmo hmi hilo holo hio hg hf

/-- The clear loop empties a register, which is the cleanup primitive. -/
example (p : Register.Program) (r base exit : Nat)
    (h0 : p[base]? = some (Register.Instruction.jzdec r exit base))
    (n : Nat) (s : Register.State) (hpc : s.pc = base) (ha : s.regs r = n) :
    Register.Reaches p s { pc := exit, regs := fun i => if i = r then 0 else s.regs i } :=
  Register.clear_reaches p r base exit h0 n s hpc ha

end LeanBF.Tests
