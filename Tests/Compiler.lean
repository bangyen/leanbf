/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Compiler

/-!
# Compiler Tests
-/

namespace LeanBF.Tests

open LeanBF

example : Compiler.movePtr 1 1 = [] :=
  rfl

example : Compiler.movePtr 0 1 = [.inc_ptr] :=
  rfl

example : Compiler.movePtr 2 0 = [.dec_ptr, .dec_ptr] :=
  rfl

example : Compiler.compileInstr (.inc1 1) =
    List.replicate 2 .inc_ptr ++ [.inc_val, .dec_ptr] ++
    List.replicate 256 .dec_val ++ [.inc_val, .dec_ptr] :=
  rfl

end LeanBF.Tests
