/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Core.Instruction
import LeanBF.Core.State

/-!
# Hello World

The classic Brainfuck program that prints `Hello World!` followed by a
newline, expressed as an `Instruction` list.

## Main definitions

* `helloWorld`: The program.
* `helloState`: The initial state the program is run from.

The program is defined for illustration only; its run behavior is not yet
machine-checked (see the Roadmap in the README).
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
  List.replicate 7 .inc_val ++ [.write] ++
  [.write, .write] ++
  List.replicate 3 .inc_val ++ [.write] ++
  List.replicate 2 .inc_ptr ++ [.write] ++
  [.dec_ptr, .dec_val, .write] ++
  [.dec_ptr, .write] ++
  List.replicate 3 .inc_val ++ [.write] ++
  List.replicate 6 .dec_val ++ [.write] ++
  List.replicate 8 .dec_val ++ [.write] ++
  List.replicate 2 .inc_ptr ++ [.inc_val, .write] ++
  [.inc_ptr] ++ List.replicate 2 .inc_val ++ [.write]

/-- The initial state of the program. -/
def helloState : State := State.mkEmpty

end LeanBF.Examples
