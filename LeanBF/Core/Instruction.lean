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

end LeanBF
