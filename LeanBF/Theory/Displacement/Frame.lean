/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Theory.Displacement.Basic

/-!
# Displacement Frames

`disp` gives a program's pointer offsets relative to wherever it starts, which
does not compose directly: chaining two programs adds the first one's net
displacement to the second one's offsets, so a bound of the form "stays within
`W` of the start" accumulates across a chain and is not preserved.

`Frame p a b W` fixes this by naming absolute cells: starting with the pointer
on `a`, the program `p` finishes on `b` and never leaves the window `[0, W]`.
Chaining is then transitive in the endpoints (`a → b`, `b → c` gives `a → c`)
with the window fixed throughout, which is what makes a long chain of appends
mechanical.

Frames for the compiler's own combinators follow: `movePtr` walks between two
cells, `clearHere` and `setHere` stay put, and a balanced loop keeps its
body's frame.

## Main definitions

* `Frame`: A program runs from one cell to another without leaving a window.

## Theorems

* `frame_append`: Frames chain through a shared middle cell.
* `frame_loop`: A loop keeps the frame of its body.
* `disp_replicate_inc_val`: Repeated `+` does not move the pointer.
* `disp_clearHere`: `clearHere` does not move the pointer.
* `disp_setHere`: `setHere` does not move the pointer.
* `frame_movePtr`: `movePtr` walks between its endpoints.
* `frame_clearHere`: `clearHere` keeps the pointer on its cell.
* `frame_setHere`: `setHere` keeps the pointer on its cell.
* `fapp`: `frame_append` with implicit programs, for readable chains.
* `frame_still`: An instruction that does not move the pointer keeps its
  frame.
* `disp_inc_val`: `+` does not move the pointer.
* `disp_dec_val`: `-` does not move the pointer.
-/

namespace LeanBF

/-- Starting with the pointer on cell `a`, the program finishes with the
    pointer on cell `b` and never leaves the window `[0, W]`. -/
def Frame (p : Program) (a b W : Int) : Prop :=
  ∃ n lo hi, disp p = some (n, lo, hi) ∧ n = b - a ∧ 0 ≤ a + lo ∧ a + hi ≤ W

/-- Frames chain through a shared middle cell, keeping the same window. -/
theorem frame_append (A B : Program) (a b c W : Int)
    (hA : Frame A a b W) (hB : Frame B b c W) : Frame (A ++ B) a c W := by
  rcases hA with ⟨na, loa, hia, hdA, hnA, hloA, hhiA⟩
  rcases hB with ⟨nb, lob, hib, hdB, hnB, hloB, hhiB⟩
  refine ⟨na + nb, min loa (na + lob), max hia (na + hib),
    disp_append A B na loa hia nb lob hib hdA hdB, by omega, ?_, ?_⟩
  · rcases min_cases loa (na + lob) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega
  · rcases max_cases hia (na + hib) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega

/-- A loop keeps the frame of its body. The body must return the pointer to
    the cell it started on, which is exactly the balance condition `disp`
    already requires of a loop. -/
theorem frame_loop (body : Program) (a W : Int)
    (h : Frame body a a W) (ha : 0 ≤ a) (haW : a ≤ W) :
    Frame [Instruction.loop body] a a W := by
  rcases h with ⟨nb, lob, hib, hdb, hnb, hlob, hhib⟩
  have hnb0 : nb = 0 := by omega
  subst hnb0
  refine ⟨0, min lob 0, max hib 0, ?_, by omega, ?_, ?_⟩
  · simp only [disp, hdb, if_pos]
  · rcases min_cases lob (0 : Int) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega
  · rcases max_cases hib (0 : Int) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega

/-- Repeating `+` leaves the pointer where it started. -/
theorem disp_replicate_inc_val : ∀ n : Nat,
    disp (List.replicate n .inc_val) = some (0, 0, 0) := by
  intro n
  induction n with
  | zero => simp only [List.replicate, disp]
  | succ k ih =>
      rw [List.replicate_succ]
      simp only [disp, ih]

/-- `clearHere` leaves the pointer where it started. -/
theorem disp_clearHere : disp Compiler.clearHere = some (0, 0, 0) := by
  simp only [Compiler.clearHere, disp]
  norm_num

/-- `setHere` leaves the pointer where it started. -/
theorem disp_setHere (n : Nat) : disp (Compiler.setHere n) = some (0, 0, 0) := by
  simp only [Compiler.setHere]
  rw [disp_append _ _ 0 0 0 0 0 0 disp_clearHere (disp_replicate_inc_val n)]
  norm_num

/-- `movePtr` walks from one cell to the other, staying between them. -/
theorem frame_movePtr (i j W : Int) (hi0 : 0 ≤ i) (hj0 : 0 ≤ j)
    (hiW : i ≤ W) (hjW : j ≤ W) : Frame (Compiler.movePtr i j) i j W := by
  rcases disp_movePtr i j with ⟨lo, hi, hd, hlo, hhi, hmax⟩
  refine ⟨j - i, lo, hi, hd, rfl, ?_, ?_⟩
  · unfold Compiler.movePtr at hd
    by_cases h : i < j
    · rw [if_pos h, disp_replicate_inc_ptr] at hd
      simp only [Option.some_inj, Prod.mk.injEq] at hd
      omega
    · rw [if_neg h, disp_replicate_dec_ptr] at hd
      simp only [Option.some_inj, Prod.mk.injEq] at hd
      omega
  · omega

/-- `clearHere` keeps the pointer on its cell. -/
theorem frame_clearHere (a W : Int) (ha : 0 ≤ a) (haW : a ≤ W) :
    Frame Compiler.clearHere a a W :=
  ⟨0, 0, 0, disp_clearHere, by omega, by omega, by omega⟩

/-- `setHere` keeps the pointer on its cell. -/
theorem frame_setHere (n : Nat) (a W : Int) (ha : 0 ≤ a) (haW : a ≤ W) :
    Frame (Compiler.setHere n) a a W :=
  ⟨0, 0, 0, disp_setHere n, by omega, by omega, by omega⟩

/-- `frame_append` with the programs implicit, so a chain of appends reads
    left to right instead of nesting. -/
theorem fapp {A B : Program} {a b c W : Int}
    (hA : Frame A a b W) (hB : Frame B b c W) : Frame (A ++ B) a c W :=
  frame_append A B a b c W hA hB

/-- A single instruction that does not move the pointer keeps its frame. -/
theorem frame_still {i : Instruction} (hd : disp [i] = some (0, 0, 0))
    (a W : Int) (ha : 0 ≤ a) (haW : a ≤ W) : Frame [i] a a W :=
  ⟨0, 0, 0, hd, by omega, by omega, by omega⟩

/-- `+` does not move the pointer. -/
theorem disp_inc_val : disp [Instruction.inc_val] = some (0, 0, 0) := by
  simp only [disp]

/-- `-` does not move the pointer. -/
theorem disp_dec_val : disp [Instruction.dec_val] = some (0, 0, 0) := by
  simp only [disp]

end LeanBF
