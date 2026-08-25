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
  `turingCompleteness_proof`. The converse holds too
  (`Theory.Simulate.Converse`): if the compiled program halts, the source
  Minsky machine halts (`minsky_halts_of_compiled_halts`), by strong
  induction on the exact length of the halting Brainfuck run. Simulation is
  therefore established in both directions, and the two halves package into
  the halting equivalence `compiled_halts_iff`: the compiled program halts
  exactly when the source machine does.
- **Register machines** (`Core.Register`, `Theory.Trace`): a counter machine
  with arbitrarily many registers, generalizing `Core.Minsky`, together with
  `runFor` — reachability counted by steps, which `Reaches` and `RunsTo`
  cannot express, being `Prop`-valued. The three divergence lemmas turn "the
  machine always has one more step" into "the machine never halts", each in
  the form a different caller can supply.
- **Arithmetic fragments** (`Theory.Transfer`, `Theory.Arith`): the loops a
  counter machine computes with — drain, scaled transfer, and exact division
  branching on the remainder — and what they build: variable multiplication,
  truncated subtraction, a comparison answering by exit address, integer
  square root by bounded search, and `Nat.pair`/`Nat.unpair`.
- **Every primitive recursive function is register computable**
  (`Theory.Universal.Primrec`): `primrec_regComputable`, an induction over
  all seven constructors of `Nat.Primrec`, with `prec` the only case whose
  sub-builder runs more than once.
- **A universal register machine** (`Theory.Universal.Machine`):
  `universal_machine` — one program whose halting is equivalent to a
  recursive code's, with the unbounded search over the step bound standing in
  for `rfind'`.
- **Packing to two counters** (`Theory.Godel`, `Theory.Packing`):
  `compile_halts_iff` — a register machine halts exactly when its two-counter
  compilation does, the file encoded as a product of prime powers and each
  instruction becoming a block that multiplies or divides by one prime. The
  packed input is `2 ^ m`.
- **Undecidability** (`Theory.Undecidable`): `universal_brainfuck` — one
  fixed Brainfuck program that halts on the tape encoding `2 ^ Nat.pair c n`
  exactly when the recursive code `c` halts on input `n`. Since the program
  is fixed and the starting tape is a computable function of the code and
  input, a decider for Brainfuck halting would decide `Nat.Partrec.Code`
  halting; `brainfuck_halting_undecidable` draws that conclusion, showing no
  computable predicate decides whether the program halts on a given input.
  The chain runs
  `Nat.Partrec.Code` → register machine (`Theory.Universal`) → two counters
  (`Theory.Packing`, via a Gödel encoding of the register file as prime
  exponents) → Minsky → Brainfuck, each link proved in both directions.
- **Concrete syntax** (`Core.Parser`): a total `parse : String → Program`,
  driven by an explicit fuel argument because a `[` continues on whatever its
  body left behind, which is not a structural subterm. Non-command characters
  are comments, an unmatched `[` runs to end of input, and an unmatched `]`
  ends the program. `parse_helloWorldSource` checks the hand-written
  `Hello World!` transcription against the source it documents, so the two
  can no longer drift apart.
- **Verified example programs** (`LeanBF.Examples`): the classic
  `Hello World!` program, machine-checked with `decide` to print exactly
  `Hello World!` and a newline and to halt, plus two concrete Minsky machines
  (`countDown`, `quadruple`) whose compiled Brainfuck programs are verified
  via `runsTo_compileProgram` to halt with the final counter values on the
  tape — and, via `run_of_RunsTo`, confirmed to complete under the
  interpreter's executable `run` in exactly `n` steps. `tripler` adds an odd
  multiplier (`c2 := 3 * c2`, where `quadruple`'s two phases both double),
  and `addMachine` computes `c2 := c1 + c2` — a result depending on both
  counters rather than on a constant built into the program.
- **Program-level I/O** (`Theory.Semantics`): a whole run consumes a prefix
  of its input (`runsTo_input_suffix`) and only extends its output
  (`runsTo_output_extends`) — nothing already written is removed or altered.
  Both lift from single-step versions by induction on the run. The output
  stream is stored most recent first, so "extends" is a prepend:
  `t.output = w ++ s.output`.
- **Loop-free termination** (`Theory.Loop.RunSeq`): a program with no `[`
  halts in exactly as many steps as it has instructions
  (`stepsToHalt_loop_free`), and therefore always halts
  (`halts_of_loopFree`).
- **Tape algebra** (`Theory.State`) and **semantics lemmas**
  (`Theory.Semantics`): the cell operations act only on the addressed cell
  and round-trip with the current value (`currentVal_incVal_decVal`), and the
  single-step behavior of every instruction — `>`, `<`, `+`, `-`, `,`, `.`,
  and `[` — is pinned down, together with I/O round-trips (read/write echo,
  reads consume the input prefix) and a divergence theorem (`[+ ]` never
  halts from a non-zero cell).
- **Program equivalence** (`Theory.Equivalence`): `ProgEquiv` — two programs
  reach the same final states from every starting state — is an equivalence
  relation and a congruence for both `++`
  (`progEquiv_append_left`/`progEquiv_append_right`, proven from
  `runsTo_append_factor`: every run of `A ++ C` factors through a state at
  which `A` has halted) and `loop` (`progEquiv_loop`, by strong induction on
  the halting run's length — each iteration costs at least the loop-entry
  step). Together these let a rewrite apply at any depth of nesting. The first instances are the cancellations `> <`,
  `< >`, and `+ -`. Their mirror image `- +` is *not* one
  (`decVal_incVal_ne_id`): cell values are natural numbers, so decrementing a
  zero cell truncates and the increment cannot recover it.
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
- **The window bound for every compiled program**
  (`Theory.Displacement.Compiler`): `frame_compileProgram` shows that the
  compiled form of *any* Minsky program keeps the pointer in cells `0` to
  `16`, so `compiled_preserves_above_window` concludes that no compiled run
  ever touches a cell above the window. This is proven from the compiler's
  structure rather than by executing a program, so it costs nothing per
  example and does not grow with the run length.
- **Syntactic pointer bounds** (`Theory.Displacement`): `disp` reads a
  program and returns the net, lowest, and highest pointer offsets it can
  reach, composing across concatenation (`disp_append`) and surviving loop
  unrolling — the crux, which works because every loop the compiler emits is
  balanced. A program whose bounds are known provably never touches a cell
  above them (`runsTo_disp_preserves_above`), with no execution involved.
  Unbalanced loops return `none`, since they move the pointer further on
  every iteration. `Frame p a b W` names absolute cells — `p` runs from `a`
  to `b` without leaving `[0, W]` — which is what composes across a chain,
  since relative offsets accumulate.
- **Compiled-run cell preservation** (`Theory.Invariance` +
  `Examples.CountDown`): `ptrBoundedRun` checks by `decide` that a concrete
  run keeps the pointer inside a window, and
  `run_preserves_tape_above_of_ptrBounded` turns that check into the
  preservation fact. Applied to `countDown`, this proves the compiled run
  never touches a tape cell above the window
  (`countDown_preserves_above_window`) — the whole 4245-step run, not just
  its final state.
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
- **Brainfuck idioms** (`Theory.Idioms`): the loops a programmer writes,
  stated on the literal instruction lists. `runsTo_moveLoop` proves `[->+<]`
  drains a cell into its right neighbour (`0` and `b + a`, pointer unmoved),
  and `runsTo_dupLoop` proves `[->+>+<<]` drains it into both neighbours
  (`0`, `b + a`, `c + a`). `[-]` is covered by `runsTo_clearHere`, which the
  compiler layer already needed. Each is tied to its source text by a `parse`
  theorem (`parse_clearHere`, `parse_moveLoop`, `parse_dupLoop`).
- **Kernel re-assertions** (`Tests`): the state, semantics, Minsky model, and
  compiler definitions are re-asserted on concrete inputs with `rfl` and
  `decide` — including running compiled Minsky programs (`inc1`, `inc2`,
  `jzdec1`, `jzdec2`, `halt`) to their halting state.

## Roadmap

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Verified Brainfuck idioms** | In progress | `Theory.Idioms` states the idioms on the literal instruction lists a programmer writes, rather than on compiler output. Three are covered. `[-]` needed no new work: `runsTo_clearHere` already proves it, since the compiler emits the same three characters as `Compiler.clearHere` for its scratch cells. `[->+<]` is the first idiom with no compiled counterpart — `runsTo_moveLoop` drains a cell into its right neighbour, leaving `0` and `b + a` with the pointer back where it started. `runsTo_dupLoop` then drains a cell into both neighbours (`0`, `b + a`, `c + a`), and it did follow from the move loop as predicted: same induction on the source cell, same loop-free body as one `runSeq` step, differing only in carrying a second neighbour through. Unbounded `Nat` cells mean no overflow side conditions, and each idiom is tied to its source text by a `parse` theorem. Still open: `[>]` scans to the next zero, which needs a hypothesis that some zero exists to the right — a different proof shape that is not expected to follow as easily. |
| **More programs verified end to end** | Low | `HelloWorld` is checked by `decide` over a thousand steps, which already required raising `maxRecDepth`. Whether that approach reaches other small classics — cat, echo, a two-cell adder — is unknown, and finding out on one program is the way to learn it. A negative result would be worth recording too. |
| **`Examples` is misnamed** | Low | Four of its five modules are Minsky machines rather than Brainfuck programs. Splitting the directory would stop it misrepresenting itself. |
| **Multiplication needs a Gödel encoding** | Done | Resolved by the universality work. The example machines (`countDown`, `quadruple`, `tripler`, `addMachine`) cover constant multiples and addition, which is the limit of what two counters express directly; a general `c2 := c1 × c2` needs three quantities live at once, so it needs an encoding. Both halves now exist: `mulVar_effect` (`Theory.Arith.Multiply`) multiplies two registers, and `Theory.Godel` packs a whole register file into one counter as a product of prime powers, which `Theory.Packing` uses to compile any register machine down to two. |
| **2CM universality bridge** | Done | Built on the `counter-machine-bridge` branch. The register-machine transfer loops (`Theory.Transfer`), the arithmetic fragments built on them (`Theory.Arith`), the induction `Nat.Primrec f → RegComputable f` (`Theory.Universal.Primrec`), the universal register machine (`Theory.Universal.Machine`), the pack down to two counters (`Theory.Packing`, the register file encoded as a product of prime powers), and the bridge to `Core.Minsky`. `universal_minsky` is the result: one Minsky program whose halting on `(2 ^ Nat.pair c n, 0)` is equivalent to code `c` halting on input `n`. Mathlib has no counter-machine model, so none of this could be adapted from it. |
| **Halting problem undecidability** | Done | `universal_brainfuck` (`Theory.Undecidable`): one fixed Brainfuck program that halts on the tape encoding `2 ^ Nat.pair c n` exactly when code `c` halts on input `n`. The program does not depend on the code or the input, and the starting tape is a computable function of both, so a decider for Brainfuck halting would decide `Nat.Partrec.Code` halting — which `ComputablePred.halting_problem` forbids. The chain is `Nat.Partrec.Code` → register machine → two counters → Minsky → Brainfuck, each link proved in both directions. |

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
