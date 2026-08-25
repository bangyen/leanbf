/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Parser
import LeanBF.Core.Semantics
import LeanBF.Examples.Brainfuck.HelloWorld

/-!
# Parser Tests

Kernel re-assertions of the parser on concrete syntax: the eight commands,
nested loops, comment characters, and the unmatched-bracket conventions.
-/

namespace LeanBF.Tests

open LeanBF

example : parse "" = ([] : Program) := rfl

example : parse "><+-,." =
    [.inc_ptr, .dec_ptr, .inc_val, .dec_val, .read, .write] := rfl

example : parse "[-]" = [.loop [.dec_val]] := rfl

/-- Loops nest, and instructions after a loop are kept. -/
example : parse "+[>[-]<]." =
    [.inc_val, .loop [.inc_ptr, .loop [.dec_val], .dec_ptr], .write] := rfl

/-- Characters outside the eight commands are comments. -/
example : parse "+ hello, world +" = [.inc_val, .read, .inc_val] := rfl

/-- An unmatched `[` runs to the end of the input. -/
example : parse "+[-" = [.inc_val, .loop [.dec_val]] := rfl

/-- An unmatched `]` ends the program. -/
example : parse "+]-" = [.inc_val] := rfl

/-- The parser agrees with the hand-written `Hello World!` transcription. -/
example : parse Examples.helloWorldSource = Examples.helloWorld :=
  Examples.parse_helloWorldSource

/-- A parsed program runs under the interpreter like any other. -/
example : (run 100 (parse "++.") State.mkEmpty).map (fun s => s.output) = some [2] := by
  decide

/-- Decidable equality lets `decide` compare programs. -/
example : parse "++" = ([.inc_val, .inc_val] : Program) := by decide

example : parse "+" ≠ ([.dec_val] : Program) := by decide

end LeanBF.Tests
