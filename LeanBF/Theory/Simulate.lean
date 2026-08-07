/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanBF.Theory.Simulate.Basics
import LeanBF.Theory.Simulate.CompileBody
import LeanBF.Theory.Simulate.CompileInstr
import LeanBF.Theory.Simulate.CompileInstrJzdec1
import LeanBF.Theory.Simulate.CompileInstrJzdec2
import LeanBF.Theory.Simulate.CompileProgram
import LeanBF.Theory.Simulate.DispatchLemmas
import LeanBF.Theory.Simulate.DispatchStep
import LeanBF.Theory.Simulate.JzdecThenElse
import LeanBF.Theory.Simulate.WindowDone
import LeanBF.Theory.Simulate.WindowInc
import LeanBF.Theory.Simulate.WindowJzdecHalt
import LeanBF.Theory.Simulate.WindowMatch
import LeanBF.Theory.Simulate.WindowSkip

/-!
# Dispatch Simulation Aggregator

This module aggregates the `LeanBF.Theory.Simulate` modules behind a single
import.
-/
