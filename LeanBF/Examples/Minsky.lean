/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanBF.Examples.Minsky.Addition
import LeanBF.Examples.Minsky.CountDown
import LeanBF.Examples.Minsky.Quadruple
import LeanBF.Examples.Minsky.Tripler

/-!
# Minsky Machine Examples Aggregator

This module aggregates the example Minsky machines behind a single import.
These are two-counter machines, not Brainfuck programs: each is compiled by
`Core.Compiler` and run to exercise the dispatch simulation. The Brainfuck
programs live under `LeanBF.Examples.Brainfuck`.
-/
