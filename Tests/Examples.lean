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

end LeanBF.Tests
