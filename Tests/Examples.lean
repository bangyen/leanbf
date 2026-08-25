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

/-- The compiled `countDown` run never touches a cell above the window. -/
example : ∃ s', run 4300 (Compiler.compileProgram Examples.countDown)
    (simState Examples.countDownStart) = some s' ∧
      ∀ i : Int, 17 ≤ i → s'.tape i = (simState Examples.countDownStart).tape i :=
  Examples.countDown_preserves_above_window

/-- The addition machine transfers `c1` into `c2`. -/
example : Minsky.RunsTo Examples.addMachine Examples.addStart Examples.addFinal :=
  Examples.add_runs

/-- Its compiled form halts with `c2 = 5` on the tape. -/
example : ∃ s', RunsTo (Compiler.compileProgram Examples.addMachine,
    simState Examples.addStart) s' ∧ s'.tape 3 = 5 := by
  rcases Examples.add_compiled with ⟨s', hrun, hpost⟩
  exact ⟨s', hrun, hpost.2.2.2.2⟩

/-- The tripler machine computes `c2 := 3 * c2`. -/
example : Minsky.RunsTo Examples.tripler Examples.triplerStart Examples.triplerFinal :=
  Examples.tripler_runs

/-- Its compiled form halts with `c2 = 6` on the tape. -/
example : ∃ s', RunsTo (Compiler.compileProgram Examples.tripler,
    simState Examples.triplerStart) s' ∧ s'.tape 3 = 6 := by
  rcases Examples.tripler_compiled with ⟨s', hrun, hpost⟩
  exact ⟨s', hrun, hpost.2.2.2.2⟩

end LeanBF.Tests
