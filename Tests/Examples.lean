/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Examples

/-!
# Example Program Tests

Kernel re-assertions of the verified example programs.
-/

namespace LeanBF.Tests

open LeanBF
open LeanBF.Examples

example : (run 1000 helloWorld helloState).map (fun s => s.output) =
    some helloWorldOutput :=
  hello_world_output

example : halts helloWorld helloState :=
  hello_world_halts

example : Minsky.RunsTo countDown countDownStart countDownFinal :=
  countDown_runs

example :
    ∃ s', RunsTo (Compiler.compileProgram countDown, simState countDownStart) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 2 :=
  countDown_compiled

example :
    ∃ s', RunsTo (Compiler.compileProgram countDown, simState countDownStart) s' :=
  countDown_halts

example :
    ∃ n s', run n (Compiler.compileProgram countDown) (simState countDownStart) = some s' ∧
      stepsToHalt (n + 1) (Compiler.compileProgram countDown) (simState countDownStart) = n ∧
        s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 2 :=
  countDown_executes

example : Minsky.RunsTo quadruple quadrupleStart quadrupleFinal :=
  quadruple_runs

example :
    ∃ s', RunsTo (Compiler.compileProgram quadruple, simState quadrupleStart) s' ∧
      s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 8 :=
  quadruple_compiled

example :
    ∃ s', RunsTo (Compiler.compileProgram quadruple, simState quadrupleStart) s' :=
  quadruple_halts

example :
    ∃ n s', run n (Compiler.compileProgram quadruple) (simState quadrupleStart) = some s' ∧
      stepsToHalt (n + 1) (Compiler.compileProgram quadruple) (simState quadrupleStart) = n ∧
        s'.ptr = 0 ∧ s'.tape 0 = 0 ∧ s'.tape 1 = 0 ∧ s'.tape 2 = 0 ∧ s'.tape 3 = 8 :=
  quadruple_executes

end LeanBF.Tests
