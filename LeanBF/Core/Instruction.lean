/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/-!
# Brainfuck Instructions

## Main definitions

* `Instruction`: The eight Brainfuck commands plus the bracketed loop.
* `Program`: A Brainfuck program (a list of instructions).
* `decEqInstruction`: Decidable equality for instructions.
* `decEqProgram`: Decidable equality for programs.
-/

namespace LeanBF

/-- Brainfuck instructions -/
inductive Instruction where
  | inc_ptr : Instruction  -- `>`
  | dec_ptr : Instruction  -- `<`
  | inc_val : Instruction  -- `+`
  | dec_val : Instruction  -- `-`
  | loop    : List Instruction → Instruction -- `[` and `]`
  | read    : Instruction  -- `,`
  | write   : Instruction  -- `.`
  deriving Repr, BEq

/-- A Brainfuck program is a list of instructions -/
abbrev Program := List Instruction

-- Decidable equality for `Instruction` and `Program`. The `deriving` handler
-- does not apply, because `loop` nests a `List Instruction`, so the two are
-- defined by mutual structural recursion.
mutual
  /-- Decidable equality for instructions, mutual with `decEqProgram`. -/
  def decEqInstruction : (a b : Instruction) → Decidable (a = b)
    | .inc_ptr, .inc_ptr => isTrue rfl
    | .dec_ptr, .dec_ptr => isTrue rfl
    | .inc_val, .inc_val => isTrue rfl
    | .dec_val, .dec_val => isTrue rfl
    | .read, .read => isTrue rfl
    | .write, .write => isTrue rfl
    | .loop a, .loop b =>
      match decEqProgram a b with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro hc; cases hc; exact h rfl)
    | .inc_ptr, .dec_ptr | .inc_ptr, .inc_val | .inc_ptr, .dec_val
    | .inc_ptr, .loop _ | .inc_ptr, .read | .inc_ptr, .write
    | .dec_ptr, .inc_ptr | .dec_ptr, .inc_val | .dec_ptr, .dec_val
    | .dec_ptr, .loop _ | .dec_ptr, .read | .dec_ptr, .write
    | .inc_val, .inc_ptr | .inc_val, .dec_ptr | .inc_val, .dec_val
    | .inc_val, .loop _ | .inc_val, .read | .inc_val, .write
    | .dec_val, .inc_ptr | .dec_val, .dec_ptr | .dec_val, .inc_val
    | .dec_val, .loop _ | .dec_val, .read | .dec_val, .write
    | .loop _, .inc_ptr | .loop _, .dec_ptr | .loop _, .inc_val
    | .loop _, .dec_val | .loop _, .read | .loop _, .write
    | .read, .inc_ptr | .read, .dec_ptr | .read, .inc_val
    | .read, .dec_val | .read, .loop _ | .read, .write
    | .write, .inc_ptr | .write, .dec_ptr | .write, .inc_val
    | .write, .dec_val | .write, .loop _ | .write, .read =>
      isFalse (by intro h; cases h)
  /-- Decidable equality for programs, mutual with `decEqInstruction`. -/
  def decEqProgram : (a b : List Instruction) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
      match decEqInstruction x y with
      | isFalse h => isFalse (by intro hc; cases hc; exact h rfl)
      | isTrue hx =>
        match decEqProgram xs ys with
        | isTrue ht => isTrue (by rw [hx, ht])
        | isFalse h => isFalse (by intro hc; cases hc; exact h rfl)
end

instance : DecidableEq Instruction := decEqInstruction

end LeanBF
