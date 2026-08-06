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
- **Completeness statement** (`Theory.Completeness`): `Simulates` (a
  Brainfuck state that simulates a Minsky state) and the conjecture
  `turingCompleteness`. The conjecture is stated but not yet proven; see the
  Roadmap.
- **Verified example program** (`LeanBF.Examples.HelloWorld`): the classic
  `Hello World!` program, machine-checked with `decide` to print exactly
  `Hello World!` and a newline and to halt.
- **Tape algebra** (`Theory.State`) and **semantics lemmas**
  (`Theory.Semantics`): the cell operations act only on the addressed cell
  and round-trip with the current value (`currentVal_incVal_decVal`), and the
  single-step behavior of the empty program, `>`, and `[` is pinned down.
- **Simulation infrastructure** (`Theory.Simulation`): a fuel-capped runner
  whose results convert into `RunsTo` chains, and the first instance — the
  compiled empty Minsky program halts from any simulating state
  (`compile_empty_simulates`).
- **Kernel re-assertions** (`Tests`): the state, semantics, Minsky model, and
  compiler definitions are re-asserted on concrete inputs with `rfl` and
  `decide` — including running compiled Minsky programs (`inc1`, `inc2`,
  `jzdec1`, `jzdec2`, `halt`) to their halting state.

## Roadmap

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Prove `turingCompleteness`** | High | `Theory/Loop` has the loop-free machinery plus `movePtr`/`runSeq` pointer, tape, and I/O lemmas. The next step is the composed `ifZeroElse` copy-loop *effect* lemma (one-iteration cell reasoning), then the flag/restore loops and the dispatch lemma. |
| **More verified examples** | Medium | Other example programs (arithmetic, loops) could follow `HelloWorld`. |
| **Run-level tape lemmas** | Low | Generalize the single-step tape lemmas to whole runs (loop unrolling, invariance). |

## Scope & Limitations

**Scope.** LeanBF formalizes the Brainfuck language — the tape, the eight
commands, the bracketed loop as a recursive instruction list, and the
small-step semantics — together with the Minsky machine model and the
compiler intended to witness Turing completeness. The completeness theorem
itself, verified example-program behavior, and any tape/stack algebra are
still open work.

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

- `turingCompleteness` is a conjecture, not a theorem: it is recorded in
  `Theory.Completeness` and re-asserted nowhere.
- The compiler and the `HelloWorld` example are verified by `decide`-checked
  runs on concrete programs, not by a general simulation theorem — that
  theorem is the `turingCompleteness` roadblock.

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
