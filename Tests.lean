/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Tests.Compiler
import Tests.Completeness
import Tests.Examples
import Tests.Loop
import Tests.Minsky
import Tests.Semantics
import Tests.State

/-!
# Test Suite Aggregator

This root test module gathers all LeanBF test modules under one import
target, making CI and local verification commands simpler.
-/
