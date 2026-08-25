# LeanBF Architecture

This document provides a technical overview of the `LeanBF` project's design
patterns and core abstractions. It is intended for developers who wish to
contribute to the formal verification of Brainfuck's Turing completeness.

## Core Abstractions

### Instructions (`LeanBF.Core.Instruction`)

`Instruction` covers the eight Brainfuck commands plus `.loop` for the
bracketed `[`/`]` pair. A loop is a *recursive list* of instructions:

- `inc_ptr` / `dec_ptr`: `>` / `<`
- `inc_val` / `dec_val`: `+` / `-`
- `loop body`: `[` and `]`, with `body : List Instruction`
- `read` / `write`: `,` / `.`

`Program` is an abbreviation for `List Instruction`, so programs are trees:
the `[`/`]` brackets are paired when the program is constructed, and no
control-flow parser is trusted at run time.

### The Machine State (`LeanBF.Core.State`)

`State` bundles the tape, pointer, and I/O:

- `ptr : Int`: the current pointer location.
- `tape : Int → Nat`: an infinite tape mapping integer indices to cell
  values, so the tape never faults and cells never underflow.
- `input : List Nat`: the remaining input stream for `,`.
- `output : List Nat`: the output stream for `.` (the most recent write is
  the head).

`State.mkEmpty` starts at cell `0` with every cell `0` and empty I/O. The
cell operations are total: `modifyCell`, `incVal`, `decVal`, `incPtr`,
`decPtr`, and `currentVal`.

### Semantics (`LeanBF.Core.Semantics`)

`step : Program → State → Option (Program × State)` is the small-step
relation. A `,` at end of input writes `0`; a `[` with current value `0`
skips its body; a non-zero `[` runs the body and then re-queues the loop
(`body ++ [instr] ++ rest`). `run` executes up to `n` steps and stops early
once the program halts; `stepsToHalt` counts the steps to halting (capped at
`n`); `haltsWithin` and `halts` express halting within `n` steps and in
general. `RunsTo : (Program × State) → State → Prop` is the
reflexive-transitive closure of `step`, and a program halts exactly when its
instruction list is empty.

### The Minsky Machine Model (`LeanBF.Core.Minsky`)

A two-counter Minsky machine (`Minsky.State`) has a program counter `pc` and
two unbounded counters `c1`, `c2`. Instructions are `inc1`, `inc2`,
`jzdec1`, `jzdec2`, and `halt`; `step` reads the instruction at `pc` and
`RunsTo` is its reflexive-transitive closure. This is the model Brainfuck
will be shown to simulate.

### The Compiler (`LeanBF.Core.Compiler`)

The compiler translates a whole Minsky program into a single Brainfuck
dispatch loop. The layout is: cell 0 is the `running` flag, cell 1 holds the
program counter `pc`, cells 2 and 3 hold `c1` and `c2`, cell 4 is the `done`
flag used by the dispatcher, and cells 5-16 back the three `ifZeroElse`
layers (the `done` test, the `pc` test, and the counter test inside `jzdec`).

The core primitive is `ifZeroElse test thenBody elseBody`, which preserves
the tested cell, runs `thenBody` exactly once when it is `0` and `elseBody`
exactly once otherwise, and restores all scratch cells to `0`. Both bodies
must start and end with the pointer on the tested cell. `compileInstr`
translates one Minsky instruction into a block that starts and ends on the
`pc` cell, and `compileProgram` assembles the `[` dispatch loop: reset
`done`, run one window per instruction (skip if already matched; test `pc`,
run the block when `0`, decrement `pc` otherwise), and stop `running` if no
window matched.

The compiled blocks and the full dispatch loop are exercised in `Tests` with
kernel `decide` reductions on small Minsky programs (`inc1`, `inc2`,
`jzdec1`, `jzdec2`, `halt`) run to their halting state.

### Parser (`LeanBF.Core.Parser`)

`parse : String → Program` reads Brainfuck concrete syntax. The recursion is
driven by an explicit fuel argument rather than the input list: a `[` parses
its body and then continues on whatever the body left behind, and that
leftover is not a structural subterm of the input, so the natural definition
does not elaborate. Fuel makes the function total by construction, and
`parse` passes the input length, which always suffices because every
recursive call consumes a character.

The parser follows the language's conventions: characters outside the eight
commands are comments and are skipped, an unmatched `[` runs to the end of
the input, and an unmatched `]` ends the program.

Example programs are written as `Instruction` lists, which makes each one a
hand transcription of the source quoted in its docstring.
`parse_helloWorldSource` closes that gap for `Hello World!` by `rfl`, so the
two representations cannot drift apart. Comparing programs this way needs
`DecidableEq Instruction`, which the `deriving` handler cannot produce
(`loop` nests a `List Instruction`); `Core.Instruction` defines it by mutual
structural recursion instead.

## The Theory Layer

Theorems are kept separate from definitions (`LeanBF/Theory`), mirroring the
project convention that `Core` files contain only definitions.

- `Theory/State.lean`: tape algebra. The cell operations act only on the
  addressed cell (`tape_modifyCell_self`/`tape_modifyCell_other`) and
  round-trip with the current value (`currentVal_incVal_decVal`), and `>`/`<`
  leave the tape and pointer alone (`incPtr_tape`, `ptr_incPtr_decPtr`).
- `Theory/Semantics.lean`: single-step semantics. Every instruction has a
  step theorem: `>`/`<` move the pointer, `+`/`-` change the current cell,
  `,` reads input (writing `0` at end-of-input), `.` writes output, and `[`
  either skips its body (zero current value) or runs it and re-queues the
  loop (non-zero). It also covers run-level I/O (`read_write_echo`,
  `runSeq_read_input` — reads consume the input prefix) and divergence
  (`loop_incVal_never_halts` — a non-zero cell makes `[+ ]` run forever).
  The empty program has no step and halts.
- `Theory/Determinism.lean`: determinism. Because `step` is a total
  function, a configuration has at most one successor
  (`step_deterministic`), the state after `n` steps is unique
  (`run_deterministic`), and at most one halting state is reachable
  (`runsTo_deterministic`, by induction on the run). The output corollaries
  (`runsTo_output_deterministic`, `runsTo_output_function`) say a program is
  a function from its input stream to its output stream.
- `Theory/Equivalence.lean`: observational equivalence. `ProgEquiv A B` holds
  when `A` and `B` reach the same final states from every starting state;
  because the reachable final state is unique (`runsTo_deterministic`), this
  says they halt on the same inputs and agree when they do. It is an
  equivalence relation and a congruence for `++`, which rests on
  `runsTo_append_factor` — the converse of `RunsTo_append`, splitting a run of
  `A ++ C` at the point where `A` halts. The instances are the pointer and
  value cancellations; `decVal_incVal_ne_id` records that `- +` is not among
  them, since `Nat` decrement truncates at zero. Congruence under `loop` is
  left open: a body runs an unbounded number of times and needs an induction
  this module does not set up.
- `Theory/Loop/` (aggregator `Theory/Loop.lean`): loop-correctness machinery.
  `Basics` has `stepOne`/`runSeq` (execute a single instruction or a whole
  loop-free program) and the `LoopFree` predicate; `RunSeq` has the run-level
  facts (`run_length_loop_free`, `run_append`, the `movePtr` run facts, and
  loop-free termination — `stepsToHalt_loop_free`/`halts_of_loopFree`);
  `CopyLoop`, `FlagLoop`, and `RestoreClear` pin down the three fixed loops
  used by `ifZeroElse`. These underpin the dispatch simulation.
- `Theory/Simulation.lean`: simulation infrastructure and the first result.
  `runToCompletion` runs until the program halts or a fuel cap is hit, and
  its results convert into `RunsTo` chains (`RunsTo_of_haltsWithin`). The
  compiled empty Minsky program is shown to halt from any simulating state
  (`compile_empty_halts`), giving the first `compile_empty_simulates`
  instance.
- `Theory/Invariance.lean`: run-level tape lemmas. `RunsTo_inv` lifts a
  configuration invariant through a `RunsTo` run, `step_preserves_tape_above`
  pins down that a single step only modifies the current cell, and
  `RunsTo_preserves_tape_above` composes them: a run whose configurations
  keep the pointer below `n` preserves every cell at or above `n`. As a
  demonstration at the compiler's footprint, `movePtr_incVal_preserves_above`
  shows the window sweep `movePtr 0 16 ++ [+ ]` preserves every cell above
  the window, and `+ -` preserves all cells at or above the pointer.
- `Theory/BodyLoop/` (aggregator `Theory/BodyLoop.lean`): the `ifZeroElse`
  then/else body loop. The loop
  `[movePtr s test ++ body ++ movePtr test s ++ clearHere]` runs an arbitrary
  `body` exactly once when the tested cell `s` is non-zero and not at all when
  it is zero, ending with the pointer back on `test` and `s` cleared. It is
  pinned down in `run` form (`run_bodyLoop_zero`/`run_bodyLoop_succ`),
  `RunsTo` form (`runsTo_bodyLoop_zero`/`runsTo_bodyLoop_succ`), and
  fuel-capped `runToCompletion` form (`runToCompletion_bodyLoop_zero`/
  `runToCompletion_bodyLoop_succ`). The `Basics` module hosts the exact-run
  bridge (`RunsExactly`, `run_of_RunsTo`) and `RunToCompletion` the
  run-composition lemmas (`runToCompletion_append`, `RunsTo_append`-style
  chaining) that the `ifZeroElse` lemma uses.
- `Theory/IfZeroElse/` (aggregator `Theory/IfZeroElse.lean`): the
  `Compiler.ifZeroElse` conditional itself. `LoopRuns` records the `RunsTo`
  forms of the three fixed loops
  (`runsTo_copyLoop`/`runsTo_flagLoop`/`runsTo_restoreLoop`), `Blocks` the
  pointer and scratch helpers (`runsTo_movePtr`, `runsTo_clearScratch`,
  `runsTo_setOne`), `Setup` the setup segment
  (`runsTo_setup_zero`/`runsTo_setup_succ`), and the main results
  `runsTo_ifZeroElse_zero`/`runsTo_ifZeroElse_succ`: from a state with
  the pointer on `test`, `Compiler.ifZeroElse` runs `thenBody` exactly once
  when the tested cell is `0` and `elseBody` exactly once otherwise,
  preserving `test` and restoring the scratch cells to `0`. `run` and
  `runToCompletion` forms follow (`run_ifZeroElse_*`,
  `runToCompletion_ifZeroElse_*`).
- `Theory/Simulate/` (aggregator `Theory/Simulate.lean`): the dispatch
  simulation. Each compiled instruction
  block is proven to update the simulating cells (`runsTo_compileInstr_*`),
  each dispatch window runs its block when the `pc` matches and skips or
  decrements otherwise (`runsTo_window_match`/`runsTo_window_skip`/
  `runsTo_window_done` and the per-instruction `runsTo_window_*`), the
  dispatch loop runs exactly the matching window (`runsTo_dispatch`, with the
  `dispatchMs`/`dispatchDone`/`dispatchRunning` effect), and the compiled
  program's loop body clears `done`, dispatches, and clears the running flag
  when no window matches (`runsTo_compileBody`). The completeness proof is in
  `CompileLoop` (`runsTo_compileProgram`, `turingCompleteness_proof`).
- `Theory/Simulate/Converse.lean`: the reverse direction. Where the forward
  proof hands the Brainfuck run over from the Minsky run, the converse
  recovers the Minsky run from the Brainfuck one
  (`minsky_halts_of_compiled_halts`), by strong induction on the exact length
  of the halting Brainfuck run. The supporting lemmas are `runsExactly_step`
  (peeling one step shortens an exact run) and `runsExactly_append_suffix`
  (a run over `B ++ C` restricted to the `C` phase is no longer than the
  whole); each loop iteration costs at least the loop-entry step, so the
  measure strictly decreases. `compiled_halts_iff` packages both directions
  as a single equivalence.
- `Theory/Completeness.lean`: `Simulates` (a Brainfuck state that simulates
  a Minsky state — pointer at cell `0`, `tape 1 = pc`, `tape 2 = c1`,
  `tape 3 = c2`, `tape 0 = 1` for running), the canonical `simState`,
  `HaltsWith` (a halted state holding a Minsky state's counters: pointer at
  `0`, running flag cleared, `c1`/`c2` in cells 2 and 3), and the statement of
  the project's central goal, `turingCompleteness` — the compiled program
  halts holding the machine's final counters. `HaltsWith` rather than
  `Simulates ms_final`, because halting clears the running flag. The proof is
  `Theory.Simulate.turingCompleteness_proof`, which bridges the
  `dispatchMs`-phrased post-condition of `runsTo_compileProgram` to
  `ms_final` via `terminal_of_RunsTo`.

## Example Programs

`LeanBF/Examples` holds example programs. `HelloWorld` is the classic
`++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.`
`+++++++..+++.` `>>.<-.<.` `+++.` `------.` `--------.` `>>+.>++.` program,
and it is verified with the kernel `decide` tactic: after 1000 steps the
output is exactly the character codes of `Hello World!` and a newline
(`hello_world_output`), and the program halts (`hello_world_halts`).

`CountDown` is a concrete two-counter Minsky machine (`jzdec1 2 1; inc2 0;
halt`) that decrements `c1` to zero while counting in `c2`. Unlike
`HelloWorld`, it exercises the compiler: `countDown_runs` proves the machine
runs to its final state, `countDown_compiled` pushes that run through
`runsTo_compileProgram` to prove the compiled Brainfuck program halts on the
canonical simulating state with `c2 = 2` on the tape, and
`countDown_executes` converts the resulting `RunsTo` chain via `run_of_RunsTo`
into an exact interpreter run: `run n` completes in exactly `n` steps
(`countDown_halts`).

`Quadruple` is a longer machine (`jzdec2 3 1; inc1 2; inc1 0; jzdec1 6 4;
inc2 5; inc2 3; halt`) that quadruples `c2` via two transfer phases and
exercises every instruction (`inc1`, `inc2`, `jzdec1`, `jzdec2`, `halt`).
`quadruple_runs` proves the 20-step run from `c2 = 2` to `c2 = 8`, and
`quadruple_compiled`/`quadruple_halts` verify the compiled program the same
way, with `quadruple_executes` giving the exact interpreter run (`c2 = 8`).

## Project Structure

- `LeanBF/Core`: Definitions (Instruction, State, Semantics, Minsky,
  Compiler, Parser).
- `LeanBF/Theory`: Theorems (tape algebra, semantics, determinism, loop
  machinery, invariance, the dispatch simulation, and completeness).
- `LeanBF/Examples`: Example programs.
- `Tests`: Executable `example` statements that re-assert the definitions.
- `scripts`: Repository guard checks (naming, imports, copyright, formatting).

## Build Notes

The project requires Mathlib pinned at `v4.28.0` (see `lakefile.toml`), and
the `Core`/`Theory` files live under the single `LeanBF` namespace. The
`maxRecDepth` and `moreLeanArgs` options are raised so that the kernel can
`decide` deep `List.replicate`-heavy terms (e.g. the compiler's 256-step
`pc`-clearing blocks) without overflowing the default recursion limit. The
`.lake/packages` sources are symlinked to the sibling LeanSharp checkout to
avoid duplicating Mathlib on disk.
