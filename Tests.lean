/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Tests.BodyLoop
import Tests.Compiler
import Tests.Completeness
import Tests.Converse
import Tests.Determinism
import Tests.Displacement
import Tests.Equivalence
import Tests.Examples
import Tests.Godel
import Tests.IfZeroElse
import Tests.Invariance
import Tests.Loop
import Tests.Minsky
import Tests.Packed
import Tests.Parser
import Tests.Register
import Tests.Semantics
import Tests.Simulate
import Tests.State
import Tests.Transfer

/-!
# Test Suite Aggregator

This root test module gathers all LeanBF test modules under one import
target, making CI and local verification commands simpler.
-/
