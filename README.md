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
pure Lean definitions — and proves two things about it.

Brainfuck is **Turing complete**: it simulates a two-counter Minsky machine
(`turingCompleteness`, closed by `Theory.Simulate`), in both directions — the
compiled program halts holding the machine's final counters, and a halting
compiled run implies the machine halts.

Brainfuck's **halting problem is undecidable**
(`brainfuck_halting_undecidable`): there is a fixed program whose halting on
a given input no computable predicate decides. The chain runs
`Nat.Partrec.Code` → register machine → two counters → Minsky → Brainfuck,
each link proved both ways, with the register file packed into two counters
by a Gödel encoding.

Every transition of the interpreter is a pure Lean function; nothing is
executed by an external trusted interpreter.

## Architecture

For a detailed overview of the project's design and the current state of the
verified theorems, see [ARCHITECTURE.md](ARCHITECTURE.md).

The implementation is organized into `Core` (definitions), `Theory`
(verified theorems — the dispatch simulation, the completeness proof, and
the run-level tape lemmas), `Examples` (example programs, split into the
Brainfuck programs and the Minsky machines that exercise the compiler), and
`Tests` (kernel re-assertions of the definitions).

## Results

The headline results, with the supporting machinery documented in
[ARCHITECTURE.md](ARCHITECTURE.md) rather than repeated here.

- **Total, deterministic interpreter** (`Core.Semantics`): `step`/`RunsTo`
  define a single-step transition on `Program × State`, with loop unrolling
  and end-of-input handled inside the pure function. It is total and
  deterministic (`Theory.Determinism`), so a program's behaviour is a
  function of its state, not a matter of interpretation.
- **The Brainfuck state machine** (`Core.State`): an infinite `Int`-indexed
  tape of unbounded `Nat` cells, pointer, input stream, and output stream.
- **The Minsky machine model** (`Core.Minsky`): a two-counter machine with
  `inc`/`jzdec` instructions and its own `RunsTo` closure.
- **The compiler** (`Core.Compiler`): a total translation of any Minsky
  program into a Brainfuck dispatch loop, exercised end-to-end in `Tests`
  with `decide`.
- **Turing completeness** (`Theory.Completeness`, `Theory.Simulate`):
  `turingCompleteness` — whenever the Minsky machine runs to `ms_final`, the
  compiled program halts with `ms_final`'s counters in cells 2 and 3. The
  converse holds too: a halting compiled run implies the machine halts, so
  the simulation is faithful in both directions rather than only sound.
- **Undecidability of Brainfuck halting** (`Theory.Undecidable`):
  `universal_brainfuck` is one fixed Brainfuck program that halts on the tape
  encoding `2 ^ Nat.pair c n` exactly when code `c` halts on input `n`. The
  program depends on neither the code nor the input and the starting tape is
  a computable function of both, so a decider for Brainfuck halting would
  decide `Nat.Partrec.Code` halting, which `ComputablePred.halting_problem`
  forbids. The chain runs `Nat.Partrec.Code` → register machine
  (`Theory.Universal`) → two counters (`Theory.Packing`, via a Gödel encoding
  of the register file as prime exponents) → Minsky → Brainfuck, each link
  proved in both directions.
- **Concrete syntax** (`Core.Parser`): a total `parse : String → Program`,
  driven by an explicit fuel argument because a `[` continues on whatever its
  body left behind, which is not a structural subterm. Every example program
  is checked against the source it documents by a `parse` theorem, so a
  transcription and its source cannot drift apart.
- **Brainfuck idioms** (`Theory.Idioms`): the loops a programmer writes,
  stated on the literal instruction lists rather than on compiler output.
  `[-]` clears a cell, `[->+<]` moves one and `[->+>+<<]` duplicates it, and
  `[>]`/`[<]` scan to the nearest zero. The scans are the interesting case:
  they do not terminate on every tape, so `runsTo_scanLoop` takes the
  distance to a zero as a parameter together with the hypothesis that no cell
  before it is zero — without that minimality the statement is false.
- **Verified example programs** (`LeanBF.Examples`, split into `Brainfuck`
  and `Minsky` by what each is written in): `cat` (`,[.,]`) is proved for
  *every* input rather than on fixed cases — `catRuns` says its output is
  `input.takeWhile (· != 0)`, so it echoes only inputs with no zero byte and
  otherwise stops early, and `cat_halts` holds unconditionally because `,`
  writes `0` at end of input. `HelloWorld` is machine-checked with `decide`
  to print exactly `Hello World!` and a newline and to halt. The Minsky
  machines (`countDown`, `quadruple`, `tripler`, `addMachine`) exercise the
  compiler, their compiled programs verified to halt with the right counters
  and to complete under the executable `run` in exactly `n` steps.
- **Kernel re-assertions** (`Tests`): the definitions are re-asserted on
  concrete inputs with `rfl` and `decide`, including compiled Minsky programs
  run to their halting state.

## Roadmap

Open work only. What the project has already proved is described under
[Results](#results) and in [ARCHITECTURE.md](ARCHITECTURE.md).

| Task | Priority | Notes |
| :--- | :--- | :--- |
| **The scan idioms' divergence** | Medium | `runsTo_scanLoop` covers `[>]` only when a zero exists to the right, and `ARCHITECTURE.md` asserts in prose that the loop diverges otherwise — a claim nothing in the development proves. The machinery is already here: `loop_incVal_never_halts` (`Theory.Semantics`) proves a Brainfuck program never halts, by strong induction showing `stepsToHalt n = n` for every fuel, and the same shape should carry over with the invariant "every cell from the pointer rightward is nonzero", which `incPtr` preserves. The hypothesis is the awkward part: an infinite tape that is nonzero everywhere to the right is a statement about infinitely many cells, so it is worth checking that it states cleanly before assuming the proof does. Closing this would also let the prose stop asserting what it cannot cite. |
| **Idioms as composable fragments** | Low | The idiom theorems are stated on a program that is exactly the idiom, so `runsTo_moveLoop` says what `[->+<]` does when it is the whole program, not when it sits inside one. The compiler layer solved this already — `Theory.Transfer` states its loops with `Reaches` and hypotheses pinning the slots a fragment occupies, precisely so fragments compose — and `RunsTo_append` is the tool. Restating the idioms that way would make them usable for proving things about real programs assembled from them, which is the point of having them. Whether it is worth the restatement depends on there being a program that wants them. |
| **More Brainfuck programs** | Low | `cat` established that `decide` is not the constraint and that the interesting statements are input-quantified. The obvious next ones are the two-cell adder `,>,[-<+>]<.` (measured: 26 steps on `3, 4`, so well within reach) and `echo`. Neither is likely to teach anything new about the semantics, which is why this is Low rather than a natural successor to the `cat` work — it would be more examples of a thing already demonstrated, not a new kind of result. |

## Scope & Limitations

**Scope.** LeanBF formalizes the Brainfuck language — the tape, the eight
commands, the bracketed loop as a recursive instruction list, and the
small-step semantics — together with the Minsky machine model, the compiler,
and the proof that `Compiler.compileProgram` simulates a two-counter Minsky
machine, so Brainfuck is Turing complete. It also formalizes the register
machine and Gödel-encoding layers needed to run the reduction the other way,
giving the undecidability of Brainfuck halting.

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
- The undecidability theorem is stated of the universal program specifically:
  no computable predicate decides whether *that* program halts on a given
  input. It is not phrased as a statement quantifying over all Brainfuck
  programs and states, which would need a computable encoding of programs
  and tapes that the project does not define.
- The compiled two-counter programs are enormous and are never run. A
  conditional on register `r` compiles to a block quadratic in `r`'s prime —
  fifty-four slots for the third register — and the register file is a
  product of prime powers, so a machine holding a few small values already
  needs a counter beyond any feasible simulation. The construction is a proof
  device, not an implementation; `compile` is also noncomputable, `regPrime`
  being defined through `Nat.nth`.

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
