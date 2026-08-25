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

/-- The calling convention is satisfiable. -/
example (p : Register.Program) (base r : Nat) :
    Register.RegComputes p base base r r (fun _ => False) id :=
  Register.regComputes_id p base r

end LeanBF.Tests
