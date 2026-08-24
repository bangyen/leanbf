/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Instruction
import LeanBF.Core.Parser
import LeanBF.Core.Semantics
import LeanBF.Core.State

/-!
# Hello World

The classic Brainfuck program that prints `Hello World!` followed by a
newline, expressed as an `Instruction` list and verified with the kernel
`decide` tactic.

## Main definitions

* `helloWorldSource`: The concrete Brainfuck source for `helloWorld`.
* `helloWorld`: The program.
* `helloState`: The initial state the program is run from.
* `helloWorldOutput`: The expected output as a list of character codes, most
  recent write first.

## Theorems

* `parse_helloWorldSource`: The program is exactly what its concrete syntax
  parses to.
* `hello_world_output`: After 1000 steps the output is exactly
  `Hello World!` and a newline.
* `hello_world_haltsWithin`: The program halts within 1000 steps.
* `hello_world_halts`: The program halts.
-/

namespace LeanBF.Examples

/--
The classic Hello World program that prints `Hello World!` followed by a
newline:
`++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.`
`+++++++..+++.` `>>.<-.<.` `+++.` `------.` `--------.` `>>+.>++.`
-/
def helloWorld : Program :=
  List.replicate 8 .inc_val ++
  [.loop (
    [.inc_ptr] ++ List.replicate 4 .inc_val ++
    [.loop (
      [.inc_ptr] ++ List.replicate 2 .inc_val ++
      [.inc_ptr] ++ List.replicate 3 .inc_val ++
      [.inc_ptr] ++ List.replicate 3 .inc_val ++
      [.inc_ptr] ++ [.inc_val] ++
      List.replicate 4 .dec_ptr ++ [.dec_val]
    )] ++
    [.inc_ptr, .inc_val, .inc_ptr, .inc_val] ++
    [.inc_ptr, .dec_val] ++
    List.replicate 2 .inc_ptr ++ [.inc_val] ++
    [.loop [.dec_ptr]] ++
    [.dec_ptr, .dec_val]
  )] ++
  List.replicate 2 .inc_ptr ++ [.write] ++
  [.inc_ptr] ++ List.replicate 3 .dec_val ++ [.write] ++
  List.replicate 7 .inc_val ++ [.write, .write] ++
  List.replicate 3 .inc_val ++ [.write] ++
  List.replicate 2 .inc_ptr ++ [.write] ++
  [.dec_ptr, .dec_val, .write] ++
  [.dec_ptr, .write] ++
  List.replicate 3 .inc_val ++ [.write] ++
  List.replicate 6 .dec_val ++ [.write] ++
  List.replicate 8 .dec_val ++ [.write] ++
  List.replicate 2 .inc_ptr ++ [.inc_val, .write] ++
  [.inc_ptr] ++ List.replicate 2 .inc_val ++ [.write]

/-- The concrete Brainfuck source for `helloWorld`. -/
def helloWorldSource : String :=
  "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]" ++
  ">>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++."

/-- The hand-written `helloWorld` program is exactly what its concrete syntax
    parses to, so the transcription in this file is machine-checked. -/
theorem parse_helloWorldSource : parse helloWorldSource = helloWorld := by
  rfl

/-- The initial state of the program. -/
def helloState : State := State.mkEmpty

/-- The output of `helloWorld`: the codes of `Hello World!` and a newline,
    most recent write first. -/
def helloWorldOutput : List Nat :=
  [10, 33, 100, 108, 114, 111, 87, 32, 111, 108, 108, 101, 72]

/-- After 1000 steps the output is exactly `Hello World!` and a newline. -/
theorem hello_world_output :
    (run 1000 helloWorld helloState).map (fun s => s.output) = some helloWorldOutput := by
  decide

/-- The program halts within 1000 steps. -/
theorem hello_world_haltsWithin : haltsWithin 1000 helloWorld helloState := by
  decide

/-- The program halts. -/
theorem hello_world_halts : halts helloWorld helloState :=
  ⟨1000, hello_world_haltsWithin⟩

end LeanBF.Examples
