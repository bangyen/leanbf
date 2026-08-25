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
halting to a search over it. Partiality then lives in exactly one place, the
outer search over the step bound, rather than threaded through every case.

## Main definitions

* `RegComputes`: A fragment computes a function, with a calling convention.

## Theorems

* `dom_iff_exists_evaln`: A code halts exactly when some step bound suffices.
* `regComputes_id`: The empty fragment computes the identity.
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

/-- A fragment computes `f` under a calling convention: started at `base`
    with the input in `inR` and every scratch register at zero, it reaches
    `exit` holding `f` of the input in `outR`, with the scratch restored.

    Restoring the scratch is what makes fragments composable, exactly as it
    was for the multiply and divide loops. -/
def RegComputes (p : Program) (base exit inR outR : Nat) (scratch : Nat → Prop)
    (f : Nat → Nat) : Prop :=
  ∀ (s : State), s.pc = base → (∀ r, scratch r → s.regs r = 0) →
    ∃ s', Reaches p s s' ∧ s'.pc = exit ∧ s'.regs outR = f (s.regs inR) ∧
      (∀ r, scratch r → s'.regs r = 0)

/-- The empty fragment computes the identity, which fixes the convention's
    orientation: no steps, input register read as output. -/
theorem regComputes_id (p : Program) (base r : Nat) :
    RegComputes p base base r r (fun _ => False) id := by
  intro s hpc hsc
  exact ⟨s, Reaches.refl s, hpc, rfl, hsc⟩

end Register

end LeanBF
