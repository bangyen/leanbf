/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Instruction

/-!
# Parser

A total parser from Brainfuck concrete syntax to `Program`. Programs are
otherwise built as Lean terms, so an example program is a hand transcription
of the source it documents; parsing the source turns that correspondence into
something the kernel checks.

The recursion is driven by an explicit fuel argument rather than the input
list. A `[` parses its body and then continues on whatever the body left
behind, and that leftover is not a structural subterm of the input, so the
natural definition does not elaborate. Fuel makes the function total by
construction, and `parse` supplies the input length, which is always enough:
every recursive call consumes at least one character.

Following the language's convention, characters outside the eight commands
are comments and are skipped. An unmatched `[` runs to the end of the input,
and an unmatched `]` ends the program.

## Main definitions

* `parseAux`: Fuel-driven parser returning a program and the unconsumed input.
* `parse`: Parse a `String` into a `Program`.
-/

namespace LeanBF

/-- Parse instructions until a closing `]` or the end of the input, returning
    the instructions parsed and the input left after the closing bracket. -/
def parseAux : Nat → List Char → Program × List Char
  | 0, rest => ([], rest)
  | _ + 1, [] => ([], [])
  | fuel + 1, c :: rest =>
    match c with
    | '[' =>
      let (body, after) := parseAux fuel rest
      let (tail, remaining) := parseAux fuel after
      (.loop body :: tail, remaining)
    | ']' => ([], rest)
    | _ =>
      let (tail, remaining) := parseAux fuel rest
      let parsed : Program :=
        match c with
        | '>' => [.inc_ptr]
        | '<' => [.dec_ptr]
        | '+' => [.inc_val]
        | '-' => [.dec_val]
        | ',' => [.read]
        | '.' => [.write]
        | _ => []
      (parsed ++ tail, remaining)

/-- Parse Brainfuck concrete syntax into a `Program`. The input length is
    always enough fuel, since every recursive call consumes a character. -/
def parse (source : String) : Program :=
  (parseAux source.toList.length source.toList).1

end LeanBF
