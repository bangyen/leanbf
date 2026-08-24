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
pure Lean definitions — and proves Brainfuck's Turing completeness by
simulating a two-counter Minsky machine (`turingCompleteness`, closed by
`Theory.Simulate`). Every transition of the interpreter is a pure Lean
function; nothing is executed by an external trusted interpreter.

## Architecture

For a detailed overview of the project's design and the current state of the
verified theorems, see [ARCHITECTURE.md](ARCHITECTURE.md).

The implementation is organized into `Core` (definitions), `Theory`
(verified theorems — the dispatch simulation, the completeness proof, and
the run-level tape lemmas), `Examples` (example programs), and `Tests`
(kernel re-assertions of the definitions).

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
  (a Brainfuck state that simulates a Minsky state), `HaltsWith` (a halted
  state holding a Minsky state's counters), and the theorem
  `turingCompleteness` — whenever the Minsky machine runs to `ms_final`, the
  compiled program halts with `ms_final`'s counters in cells 2 and 3. It is
  proven by the dispatch simulation in `Theory.Simulate` and closed by
  `turingCompleteness_proof`.
- **Verified example programs** (`LeanBF.Examples`): the classic
  `Hello World!` program, machine-checked with `decide` to print exactly
  `Hello World!` and a newline and to halt, plus two concrete Minsky machines
  (`countDown`, `quadruple`) whose compiled Brainfuck programs are verified
  via `runsTo_compileProgram` to halt with the final counter values on the
  tape — and, via `run_of_RunsTo`, confirmed to complete under the
  interpreter's executable `run` in exactly `n` steps.
- **Tape algebra** (`Theory.State`) and **semantics lemmas**
  (`Theory.Semantics`): the cell operations act only on the addressed cell
  and round-trip with the current value (`currentVal_incVal_decVal`), and the
  single-step behavior of every instruction — `>`, `<`, `+`, `-`, `,`, `.`,
  and `[` — is pinned down, together with I/O round-trips (read/write echo,
  reads consume the input prefix) and a divergence theorem (`[+ ]` never
  halts from a non-zero cell).
- **Determinism** (`Theory.Determinism`): the interpreter is deterministic —
  `step` is a total function, so a configuration has at most one successor
  (`step_deterministic`), the state after `n` steps is unique
  (`run_deterministic`), and at most one halting state is reachable from a
  configuration (`runsTo_deterministic`). It follows that a program is a
  function from its input stream to its output stream
  (`runsTo_output_deterministic`, `runsTo_output_function`).
- **Simulation infrastructure** (`Theory.Simulation`): a fuel-capped runner
  whose results convert into `RunsTo` chains, and the first instance — the
  compiled empty Minsky program halts from any simulating state
  (`compile_empty_simulates`).
- **Run-level tape invariance** (`Theory.Invariance`): `RunsTo_inv` (a
  general configuration invariant), `step_preserves_tape_above` (a single
  step only modifies the current cell), and `RunsTo_preserves_tape_above`
  (a pointer-bounded run preserves every cell at or above the bound) —
  applied to the compiler's window sweep (`movePtr 0 16 ++ [+ ]`) to show
  cells above the window survive the run.
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
| **Completeness converse** | Medium | The reverse direction: if `Compiler.compileProgram m` halts from `simState ms`, then `m` halts from `ms`. Needs an invariant over the dispatch loop showing every halting Brainfuck run is tracked by a Minsky run — substantially harder than the forward direction, which the compiler hands over directly. |
| **More verified examples** | Medium | More Minsky machines (e.g. a multiplication machine `c2 := c1 × c2`) could run through `runsTo_compileProgram` like `countDown` and `quadruple`. |
| **Compiled-run cell preservation** | Low | Push the pointer-position invariant through all reachable fragments of a compiled Minsky body, so the whole compiled `countDown`/`quadruple` run provably never touches tape cells above 16 (beyond the current window-sweep demonstration in `Theory.Invariance`). |
| **Program-level I/O functionality** | Low | Generalize the existing `read_write_echo`/`runSeq_read_input` single-instruction I/O facts to whole programs: a run's reads consume a prefix of the input and its writes append to the output. |
| **Loop-free programs always halt** | Low | A `LoopFree` program terminates in exactly as many steps as it has instructions; a `halts`-level corollary of `run_length_loop_free` (`Theory.Loop.RunSeq`). |
| **Halting problem undecidability** | High | The capstone: `turingCompleteness` plus the classical fact that two-counter-machine halting is undecidable. Blocked on an external computability library, as mathlib does not contain the classical 2CM universality result. |

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
  shows `Compiler.compileProgram` simulates the two-counter Minsky machine and
  halts holding its final counters (`HaltsWith`). The halting state is not
  `Simulates ms_final`: the dispatch loop clears the running flag on halting,
  so cell `0` is `0` where `Simulates` demands `1`.
- Completeness is one-directional: a halting compiled Brainfuck run is not yet
  proven to imply that the source Minsky machine halts.

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
