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

## The Theory Layer

Theorems are kept separate from definitions (`LeanBF/Theory`), mirroring the
project convention that `Core` files contain only definitions.

- `Theory/State.lean`: tape algebra. The cell operations act only on the
  addressed cell (`tape_modifyCell_self`/`tape_modifyCell_other`) and
  round-trip with the current value (`currentVal_incVal_decVal`), and `>`/`<`
  leave the tape and pointer alone (`incPtr_tape`, `ptr_incPtr_decPtr`).
- `Theory/Semantics.lean`: single-step semantics. The empty program has no
  step, `>` moves the pointer, and `[` either skips its body (zero current
  value) or runs it and re-queues the loop (non-zero). The empty program
  halts.
- `Theory/Loop.lean`: loop-correctness machinery. `stepOne`/`runSeq` execute
  a single instruction or a whole loop-free program, `LoopFree` characterizes
  programs without `[`, and `run_length_loop_free`/`run_append` let a run be
  split across a loop-free prefix and its tail. These underpin the dispatch
  simulation.
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
- `Theory/BodyLoop.lean`: the `ifZeroElse` then/else body loop. The loop
  `[movePtr s test ++ body ++ movePtr test s ++ clearHere]` runs an arbitrary
  `body` exactly once when the tested cell `s` is non-zero and not at all when
  it is zero, ending with the pointer back on `test` and `s` cleared. It is
  pinned down in `run` form (`run_bodyLoop_zero`/`run_bodyLoop_succ`),
  `RunsTo` form (`runsTo_bodyLoop_zero`/`runsTo_bodyLoop_succ`), and
  fuel-capped `runToCompletion` form (`runToCompletion_bodyLoop_zero`/
  `runToCompletion_bodyLoop_succ`). The module also hosts the exact-run bridge
  (`RunsExactly`, `run_of_RunsTo`) and the run-composition lemmas
  (`runToCompletion_append`, `RunsTo_append`-style chaining) that the
  `ifZeroElse` lemma will use.
- `Theory/IfZeroElse.lean`: the `Compiler.ifZeroElse` conditional itself. It
  records the `RunsTo` forms of the three fixed loops
  (`runsTo_copyLoop`/`runsTo_flagLoop`/`runsTo_restoreLoop`), the pointer and
  scratch helpers (`runsTo_movePtr`, `runsTo_clearScratch`, `runsTo_setOne`),
  the setup segment (`runsTo_setup_zero`/`runsTo_setup_succ`), and the main
  results `runsTo_ifZeroElse_zero`/`runsTo_ifZeroElse_succ`: from a state with
  the pointer on `test`, `Compiler.ifZeroElse` runs `thenBody` exactly once
  when the tested cell is `0` and `elseBody` exactly once otherwise,
  preserving `test` and restoring the scratch cells to `0`. `run` and
  `runToCompletion` forms follow (`run_ifZeroElse_*`,
  `runToCompletion_ifZeroElse_*`).
- `Theory/Simulate.lean`: the dispatch simulation. Each compiled instruction
  block is proven to update the simulating cells (`runsTo_compileInstr_*`),
  each dispatch window runs its block when the `pc` matches and skips or
  decrements otherwise (`runsTo_window_match`/`runsTo_window_skip`/
  `runsTo_window_done` and the per-instruction `runsTo_window_*`), the
  dispatch loop runs exactly the matching window (`runsTo_dispatch`, with the
  `dispatchMs`/`dispatchDone`/`dispatchRunning` effect), and the compiled
  program's loop body clears `done`, dispatches, and clears the running flag
  at a halt (`runsTo_compileBody`, `runsTo_compileProgram`). This proves
  `turingCompleteness_proof`: Brainfuck simulates the two-counter Minsky
  machine.
- `Theory/Completeness.lean`: `Simulates` (a Brainfuck state that simulates
  a Minsky state — pointer at cell `0`, `tape 1 = pc`, `tape 2 = c1`,
  `tape 3 = c2`, `tape 0 = 1` for running), the canonical `simState`, and
  the statement of the project's central goal, `turingCompleteness`. The
  proof is `Theory.Simulate.turingCompleteness_proof`.

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
  Compiler).
- `LeanBF/Theory`: Theorems (currently only the Completeness statement).
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
