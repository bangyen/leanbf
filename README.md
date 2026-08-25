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
`Theory.Simulate`), in both directions: the compiled program halts holding
the machine's final counters, and a halting compiled run implies the machine
halts. Every transition of the interpreter is a pure Lean
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
  `turingCompleteness_proof`. The converse holds too
  (`Theory.Simulate.Converse`): if the compiled program halts, the source
  Minsky machine halts (`minsky_halts_of_compiled_halts`), by strong
  induction on the exact length of the halting Brainfuck run. Simulation is
  therefore established in both directions, and the two halves package into
  the halting equivalence `compiled_halts_iff`: the compiled program halts
  exactly when the source machine does.
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
- **Kernel re-assertions** (`Tests`): the state, semantics, Minsky model, and
  compiler definitions are re-asserted on concrete inputs with `rfl` and
  `decide` — including running compiled Minsky programs (`inc1`, `inc2`,
  `jzdec1`, `jzdec2`, `halt`) to their halting state.

## Roadmap

| Task | Priority | Status |
| :--- | :--- | :--- |
| **Multiplication needs a Gödel encoding** | Low | The example machines (`countDown`, `quadruple`, `tripler`, `addMachine`) cover constant multiples and addition, which is the limit of what two counters express directly. A general `c2 := c1 × c2` needs three quantities live at once — counter, multiplicand, accumulator — so it requires encoding two values in one register (`c1 = 2^a · 3^b`). That is the same construction the 2CM universality bridge needs, and is not a small example task. |
| **2CM universality bridge** | High | The remaining capstone input, being built on the `counter-machine-bridge` branch. Done: the register-machine transfer loops (`Theory.Transfer`), the arithmetic fragments built on them (`Theory.Arith` — variable multiplication, truncated subtraction, comparison answering by exit address, integer square root, `Nat.pair` and `Nat.unpair`), the induction `Nat.Primrec f → RegComputable f` (`Theory.Universal.Primrec`), the universal register machine (`Theory.Universal.Machine` — `universal_machine` proves `(∃ t, RunsTo U (loopState (Nat.pair c n) 0) t) ↔ (Code.eval (ofNat Code c) n).Dom`, the unbounded search over the step bound standing in for `rfind'`), and the pack down to two counters (`Theory.Packing`). `compile_halts_iff` proves a register machine halts exactly when its two-counter compilation does, the register file encoded as a product of prime powers (`Theory.Godel`) and each instruction becoming a block that multiplies or divides by one prime. The packed input is `2 ^ m`, concrete enough for a reduction to name. Still to build: the bridge from two-register `Register` programs to `Core.Minsky`, which is a lockstep bisimulation — the two step relations are structurally identical. Mathlib has no counter-machine model, so none of this can be adapted from it. |
| **Halting problem undecidability** | High | The capstone: Brainfuck halting is undecidable. Every piece but one is now in place. `compiled_halts_iff` reduces 2CM halting to Brainfuck halting, `universal_machine` reduces `Nat.Partrec.Code` halting to register machine halting, and `compile_halts_iff` reduces register machine halting to two counters. What remains is to join the last two — a lockstep bisimulation between two-register `Register` programs and `Core.Minsky` — and then to contradict `ComputablePred.halting_problem`. |

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
