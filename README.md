# LeanBF

**Formal Verification of the Brainfuck Esolang in Lean 4.**

[![CI](https://github.com/bangyen/leanbf/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/bangyen/leanbf/actions/workflows/lean_action_ci.yml)
[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanBF formalizes the [Brainfuck](https://en.wikipedia.org/wiki/Brainfuck)
esolang in the [Lean 4](https://leanprover.github.io/) interactive theorem
prover. It pins down a precise, total, deterministic formalization — the
tape, the instruction set, and a small-step operational semantics are all
pure Lean definitions — and its long-term goal is a machine-checked proof of
Brainfuck's Turing completeness by simulating a two-counter Minsky machine.
Every transition of the interpreter is a pure Lean function; nothing is
executed by an external trusted interpreter.

## Architecture

For a detailed overview of the project's design and the current state of the
verified theorems, see [ARCHITECTURE.md](ARCHITECTURE.md).

The implementation is organized into `Core` (definitions), `Theory`
(verified theorems — currently the `turingCompleteness` statement), `Examples`
(example programs), and `Tests` (kernel re-assertions of the definitions).

## Results

- **Total, deterministic interpreter** (`Core.Semantics`): `step`/`RunsTo`
  define a single-step transition on `Program × State`, with loop unrolling
  and end-of-input handled inside the pure function.
- **The Brainfuck state machine** (`Core.State`): an infinite `Int`-indexed
  tape of unbounded `Nat` cells, pointer, input stream, and output stream.
- **The Minsky machine model** (`Core.Minsky`): a two-counter machine with
  `inc`/`jzdec` instructions and its own `RunsTo` closure.
- **The compiler** (`Core.Compiler`): a total translation of any Minsky
  program into a Brainfuck dispatch loop. `ifZeroElse` is a value-preserving
  conditional, and `compileInstr`/`compileProgram` assemble the loop. The
  compiled programs are exercised end-to-end in `Tests` with `decide`.
- **Completeness** (`Theory.Completeness` + `Theory.Simulate`): `Simulates`
  (a Brainfuck state that simulates a Minsky state) and the theorem
  `turingCompleteness`, proven by the dispatch simulation in
  `Theory.Simulate` and closed by `turingCompleteness_proof`.
- **Verified example programs** (`LeanBF.Examples`): the classic
  `Hello World!` program, machine-checked with `decide` to print exactly
  `Hello World!` and a newline and to halt, and `countDown` — a concrete
  Minsky machine whose compiled Brainfuck program is verified via
  `runsTo_compileProgram` to halt with the final counter values on the tape.
- **Tape algebra** (`Theory.State`) and **semantics lemmas**
  (`Theory.Semantics`): the cell operations act only on the addressed cell
  and round-trip with the current value (`currentVal_incVal_decVal`), and the
  single-step behavior of the empty program, `>`, and `[` is pinned down.
- **Simulation infrastructure** (`Theory.Simulation`): a fuel-capped runner
  whose results convert into `RunsTo` chains, and the first instance — the
  compiled empty Minsky program halts from any simulating state
  (`compile_empty_simulates`).
- **Body-loop machinery** (`Theory.BodyLoop`): the `ifZeroElse` then/else
  loops — `[movePtr s test ++ body ++ movePtr test s ++ clearHere]` — run an
  arbitrary body program exactly once when the tested cell is non-zero and not
  at all when it is zero. This is proven in `run`, `RunsTo`, and
  `runToCompletion` form (`runsTo_bodyLoop_zero`/`runsTo_bodyLoop_succ`), and
  the module also hosts the exact-run bridge (`RunsExactly`) and the
  run-composition lemmas (`runToCompletion_append`) used to chain loop
  effects.
- **The `ifZeroElse` conditional** (`Theory/IfZeroElse`): chains the four loop
  effects into the behavior of `Compiler.ifZeroElse` itself. From a state with
  the pointer on `test`, the compiled conditional runs `thenBody` exactly once
  when `test` is `0` and `elseBody` exactly once otherwise, preserving `test`
  and restoring the scratch cells to `0` (`runsTo_ifZeroElse_zero`/
  `runsTo_ifZeroElse_succ`, plus `run` and `runToCompletion` forms).
- **Kernel re-assertions** (`Tests`): the state, semantics, Minsky model, and
  compiler definitions are re-asserted on concrete inputs with `rfl` and
  `decide` — including running compiled Minsky programs (`inc1`, `inc2`,
  `jzdec1`, `jzdec2`, `halt`) to their halting state.

## Roadmap

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Prove `turingCompleteness`** | High | Done. `Theory.Simulate` wires `compileInstr`/`compileProgram` into the dispatch simulation: each window runs its instruction's block, the dispatch loop runs exactly the matching window, the loop body maps a simulating state to the stepped machine, and `turingCompleteness_proof` closes the statement by induction on `Minsky.RunsTo`. |
| **More verified examples** | Medium | More Minsky machines (arithmetic, multiplication) could run through `runsTo_compileProgram` like `countDown`. |
| **Run-level tape lemmas** | Low | Generalize the single-step tape lemmas to whole runs (loop unrolling, invariance). |

## Scope & Limitations

**Scope.** LeanBF formalizes the Brainfuck language — the tape, the eight
commands, the bracketed loop as a recursive instruction list, and the
small-step semantics — together with the Minsky machine model, the compiler,
and the proof that `Compiler.compileProgram` simulates a two-counter Minsky
machine, so Brainfuck is Turing complete.

**Design choices.** Brainfuck's informal specification leaves several details
open; LeanBF makes the following choices, documented in `ARCHITECTURE.md`:

- **Infinite tape**: cells live on an `Int`-indexed tape with unbounded `Nat`
  values, so pointer arithmetic never faults and decrement never underflows.
- **Loops as trees**: `[`/`]` are paired at definition time; `loop body` is a
  recursive `List Instruction`. At runtime a non-zero loop pushes
  `body ++ [loop body] ++ rest`, so no control-flow parser is trusted.
- **Input/output**: `,` consumes from an explicit `List Nat` input stream
  (pushing `0` at EOF); `.` prepends the current cell to the output stream.
- **Halting**: a program halts exactly when its instruction list is empty.

**Limitations.**

- The completeness theorem is proven: `Theory.Simulate.turingCompleteness_proof`
  shows `Compiler.compileProgram` simulates the two-counter Minsky machine.

## Installation & Building

Make sure you have [elan](https://github.com/leanprover/elan) installed for
Lean 4 version management.

```bash
git clone https://github.com/bangyen/leanbf.git
cd leanbf
lake exe cache get  # Downloads the pre-compiled Mathlib libraries
lake build
```

Then run the verification:

```bash
lake test           # Builds the test suite
lake lint           # Runs the linter
./scripts/check_all.sh  # Runs the repository guard checks
```

## Contributing

This repo uses standard Mathlib naming conventions and the same guard scripts
as LeanSharp. If you are interested in extending the formalization — for
example, completing the `jzdec` translation or taking a first step toward the
completeness proof — feel free to open a pull request.

## Citation

If you use this work in your research, please cite:

```bibtex
@misc{pham_leanbf_2026,
  author = {Pham, Bangyen},
  title = {LeanBF: Formal Verification of the Brainfuck Esolang in Lean 4},
  year = {2026},
  url = {https://github.com/bangyen/leanbf}
}
```
