# LeanBF Architecture

This document provides a technical overview of the `LeanBF` project's design
patterns and core abstractions. It is intended for developers who wish to
contribute to the formal verification of Brainfuck's Turing completeness and
of the undecidability of its halting problem.

The two results are the two halves of the same simulation. Completeness
compiles a two-counter machine into Brainfuck; undecidability builds a
two-counter machine whose halting is as hard as the halting problem, and
compiles that. The first half is `Core.Compiler` with `Theory.Simulate` and
`Theory.Completeness`; the second is everything under `Theory.Universal` and
`Theory.Packing`, closed by `Theory.Undecidable`.

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
  The empty program has no step and halts. The single-instruction I/O facts
  are also lifted to whole runs: `runsTo_input_suffix` says a run's reads
  consume a prefix of the input, and `runsTo_output_extends` says a run only
  extends the output. Because the output stream is stored most recent first,
  that extension is a prepend (`t.output = w ++ s.output`).
- `Theory/Determinism.lean`: determinism. Because `step` is a total
  function, a configuration has at most one successor
  (`step_deterministic`), the state after `n` steps is unique
  (`run_deterministic`), and at most one halting state is reachable
  (`runsTo_deterministic`, by induction on the run). The output corollaries
  (`runsTo_output_deterministic`, `runsTo_output_function`) say a program is
  a function from its input stream to its output stream.
- `Theory/Displacement.lean`: syntactic pointer bounds. `disp` returns a
  program's `(net, lo, hi)` pointer offsets, or `none` for a loop whose body
  has non-zero net displacement, since such a loop moves further on every
  iteration. Bounds compose across `++` (`disp_append`) and are preserved by
  `step`; the crux is the loop-unroll case, where `body ++ [loop body] ++
  rest` keeps the original bounds exactly because the body's net is zero.
  `runsTo_disp_preserves_above` then concludes that a run never touches a
  cell above its bound. `Frame` (in `Displacement/Frame.lean`) names absolute
  cells rather than relative offsets — `Frame p a b W` says `p` runs from
  cell `a` to cell `b` without leaving `[0, W]` — which is what makes long
  chains compose, since relative bounds accumulate across appends.
  `Displacement/Compiler.lean` frames each compiler combinator in turn and
  concludes `compiled_preserves_above_window`: every compiled Minsky program
  keeps the pointer within cells 0 to 16, so no compiled run touches anything
  above the window. This supersedes the per-example `decide` check, which did
  not scale past `countDown`. Unlike `Invariance.ptrBoundedRun`, which executes one
  concrete run, this bounds every run of a program without reference to a
  starting state.
- `Theory/Equivalence.lean`: observational equivalence. `ProgEquiv A B` holds
  when `A` and `B` reach the same final states from every starting state;
  because the reachable final state is unique (`runsTo_deterministic`), this
  says they halt on the same inputs and agree when they do. It is an
  equivalence relation and a congruence for `++`, which rests on
  `runsTo_append_factor` — the converse of `RunsTo_append`, splitting a run of
  `A ++ C` at the point where `A` halts. The instances are the pointer and
  value cancellations; `decVal_incVal_ne_id` records that `- +` is not among
  them, since `Nat` decrement truncates at zero. It is also a congruence for
  `loop` (`progEquiv_loop`): a body runs an unbounded number of times, so the
  proof is a strong induction on the length of the halting run, which
  strictly decreases because each iteration costs at least the loop-entry
  step. The counting lemmas this needs (`runsExactly_step`,
  `runsExactly_append_suffix`) live in `Theory/BodyLoop/Basics.lean` beside
  `RunsExactly` itself, since they are generic run arithmetic rather than
  anything compiler-specific.
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
  For whole compiled runs the module also provides `ptrBoundedRun`, an
  executable check that the pointer stays below a bound at every step, and
  `run_preserves_tape_above_of_ptrBounded`, which converts a successful check
  into cell preservation. `Examples.CountDown` discharges the check by
  `decide` and concludes that the compiled run never touches a cell above the
  window. The same argument does not currently scale to `quadruple`: at 35451
  steps against `countDown`'s 4245, kernel reduction exceeds the heartbeat
  limit.
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
- `Theory/Idioms.lean`: the loops a Brainfuck programmer writes, stated on
  the literal instruction lists rather than on compiler output. Everything
  else in this layer reasons about loops `Core.Compiler` emitted, laid out
  over scratch cells the compiler chose; the idioms take the pointer's own
  cells as their only parameters. `runsTo_moveLoop` is the result for
  `[->+<]`: from `a` at the pointer and `b` beside it, the loop ends with `0`
  and `b + a`, the pointer back on the drained cell so the fragment composes
  with what follows. `runsTo_dupLoop` is the same for `[->+>+<<]`, draining
  into both neighbours to leave `0`, `b + a` and `c + a`. Unbounded `Nat`
  cells mean no overflow side condition. Both proofs have the shape of
  `runsTo_clearHere` — induction on the source cell, the loop-free body
  (`loop_free_moveLoopBody`, `loop_free_dupLoopBody`) discharged as one
  `runSeq` step (`runSeq_moveLoopBody`, `runSeq_dupLoopBody`), and
  `RunsTo_append` chaining the iteration onto the recursive call; the
  duplicate loop differs only in carrying a second neighbour through the
  induction. Each idiom is tied back to its source characters by `rfl`
  (`parse_moveLoop`, `parse_dupLoop`). `[-]` needs nothing new here:
  `runsTo_clearHere` already proves it, since the compiler emits the same
  three characters as `Compiler.clearHere` for its scratch cells;
  `parse_clearHere` gives it the same tie to source text.
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

## The Undecidability Layer

The completeness half compiles a Minsky machine *into* Brainfuck. This half
runs the reduction the other way: it builds a machine whose halting is as
hard as the halting problem, so that Brainfuck's halting inherits that
hardness. It is the larger half, because a two-counter machine is a
deliberately impoverished target and every arithmetic fragment had to be
built from `inc`, `jzdec` and `halt`. Mathlib has no counter-machine model,
so none of it could be adapted.

The chain runs `Nat.Partrec.Code` → register machine → two counters → Minsky
→ Brainfuck, each link proved in both directions.

### Register machines and their traces

- `Core/Register.lean`: a counter machine with arbitrarily many registers,
  generalizing `Core.Minsky`, whose two counters are fixed in the state
  structure. Registers are a total function `Nat → Nat` rather than a tuple,
  so a program can name any register without carrying a bound. This is the
  middle layer: recursive functions are naturally simulated by a machine with
  as many registers as the construction needs, and only afterwards are those
  packed into two.
- `Theory/Trace.lean`: reachability counted by steps. `Reaches` and `RunsTo`
  are `Prop`-valued, so a derivation carries no number and nothing can be
  proved by induction on one; `runFor` supplies it. The module's three
  divergence lemmas say a machine never halts, each the convenient form for a
  different caller: `no_runsTo_of_steps_rel` names its stages by a relation
  (a simulation cannot name them by a function of the step number — how far
  the simulating machine travels per source step depends on the source
  instruction), `no_runsTo_of_steps` by a function, and
  `no_runsTo_of_diverges` by a function whose consecutive stages visibly
  differ. Each is proved from the one above it.
- `Theory/Embed.lean`: `EmbeddedAt`, saying a program contains a fragment at
  an address without constraining the rest of it, so one program can host
  many fragments side by side. `flatMap_getElem_prefix` indexes a
  concatenation by piece and offset, which the compiler needs because its
  blocks differ in size; `flatMap_getElem_uniform` is the special case for
  equal-sized pieces, which the padded restore arms use to get closed-form
  addresses.

### Arithmetic fragments

- `Theory/Transfer.lean`: the loops everything else is built from. `drain`
  empties one register into another, `kdrain` transfers `k` units at a time
  (multiplying by `k`), and `div` consumes groups of `k` and branches on the
  remainder by exit address. `copyBack` is the non-destructive copy, which
  needs one scratch register to pour back from.
- `Theory/Arith.lean`: the fragments built on those loops — variable
  multiplication (`mulVar_effect`), truncated subtraction, a comparison that
  answers by which address it exits at, integer square root by bounded
  search, and `Nat.pair`/`Nat.unpair`. The pairing fragment is fifty-one
  slots and leaves both operands as it found them, which is what lets the
  same input be read twice.

### The universal register machine

- `Theory/Universal/Convention.lean`: `Computes`, the calling convention the
  fragments share — a scratch region `[lo, hi)` disjoint from the named
  registers, so disjointness side conditions are arithmetic rather than set
  reasoning, and a frame clause without which sequencing is not provable.
  `dom_iff_exists_evaln` reduces halting to a search over a decidable
  predicate, which is what lets a total machine express a function that need
  not terminate.
- `Theory/Universal/Builder.lean`: `Builds`, a relocatable builder. Two
  `RegComputable` witnesses cannot be combined — each binds its own program,
  and the jump targets inside are absolute — so the induction is over
  builders, and concatenating two is list append with the second handed
  `base + first.length`.
- `Theory/Universal/Primrec.lean`: the induction `Nat.Primrec f →
  RegComputable f`, discharging all seven constructors. `prec` is the only
  case whose sub-builder runs more than once; the step function's fragment is
  placed once inside the loop body and applied afresh on each pass.
- `Theory/Universal/Search.lean`: `evalnPacked`, the step-bounded evaluator
  on one packed argument. `primrec_evaln` says the interpreter is primitive
  recursive in all three of its arguments, the code number included, which is
  what keeps the seven cases from having to be redone over
  `Nat.Partrec.Code`. The `Option` result is encoded as `Encodable.encode`
  already encodes it, which makes the search's test free: `jzdec` jumps when
  a register is zero and decrements otherwise, so the instruction that
  detects success is also the one that decodes it.
- `Theory/Universal/Machine.lean`: `universal_machine`, one program whose
  halting from `loopState (Nat.pair c n) 0` is equivalent to code `c` halting
  on `n`. Because every fragment restores what it borrows, the state at the
  top of the next iteration is literally `loopState` with the bound raised,
  which is what keeps both directions short.

### Packing down to two counters

- `Theory/Godel.lean`: a register file as a single number, register `r`
  holding `padicValNat (p r) n` for distinct primes `p`. Incrementing
  multiplies by `p r`, decrementing divides, and testing for zero asks
  whether `p r` divides — the three facts the machine layer realizes as
  loops.
- `Theory/Packing/Support.lean`: `packRange`, the packed value over a bounded
  range, with `MentionsBelow` supplying the bound — a program names finitely
  many registers, and `exists_mentionsBelow` produces one, which is what lets
  a machine that only exists inside an existential be packed at all. Updating
  one register multiplies or divides the packed value by that register's
  prime (`packRange_setReg_succ` and its twin), which is a fact about the
  product rather than about a valuation. `packRange_init` says a file holding
  one number in register zero packs to `2 ^ m`, which is what makes the
  reduction map concrete.
- `Theory/Packing/Blocks.lean` and `Divide.lean`: what one instruction
  becomes. An increment is a scaled transfer; a conditional is a single
  divide, which answers the zero test and performs the decrement at once. The
  divide is destructive, so each non-zero remainder gets a restore arm that
  multiplies the quotient back and adds that remainder as literal units.
  Every block opens with a no-op testing the empty scratch counter, which
  makes its run provably non-empty even when the block exits to its own base
  — as it does whenever a source instruction jumps to itself.
- `Theory/Packing/Compile.lean`: `layout`, the address table. Defining it by
  `List.take` is what makes an out-of-range jump behave: taking more than a
  list holds gives the whole list, so a target past the end of the source
  maps to the end of the compiled program, out of bounds there too.
- `Theory/Packing/Simulate.lean`: `compile_halts_iff`. The Gödel translation
  happens in `step_simulates` and nowhere else — a register is zero exactly
  when its prime fails to divide the packed value, so the two branches of the
  conditional block are the two branches of the instruction.
- `Theory/Packing/Minsky.lean`: the last step down, and the shortest. A
  program naming only registers zero and one is already a Minsky machine
  written differently, so the two step relations are the same relation on
  different state types and one step matches one step.

### The capstone

- `Theory/Undecidable.lean`: `universal_brainfuck`, one fixed Brainfuck
  program that halts on the tape encoding `2 ^ Nat.pair c n` exactly when
  code `c` halts on input `n`, and `brainfuck_halting_undecidable`, which
  draws the conclusion: no computable predicate decides whether that program
  halts on a given input. The program does not depend on the code or the
  input, and the starting tape is a computable function of both, so a decider
  would contradict `ComputablePred.halting_problem`.

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

`Tripler` (`c2 := 3 * c2`, 14 steps) is the odd-multiplier companion, since
both of `Quadruple`'s phases double. `Addition` (`c2 := c1 + c2`, 5 steps) is
the one example whose result depends on both counters rather than on a
constant fixed in the program. That was the boundary of what the examples
could reach: a general `c2 := c1 * c2` needs the counter, the multiplicand,
and the accumulator live at once, which two registers cannot hold directly.
The undecidability layer crosses it — `Theory.Arith.Multiply` multiplies two
registers of a machine that has enough of them, and `Theory.Packing` packs
any such machine back down to two — but the examples themselves stop here,
being about the compiler rather than about that construction.

## Project Structure

- `LeanBF/Core`: Definitions (Instruction, State, Semantics, Minsky,
  Register, Compiler, Parser).
- `LeanBF/Theory`: Theorems. The completeness half — tape algebra, semantics,
  determinism, loop machinery, invariance, the dispatch simulation — the
  undecidability half, in `Trace`, `Embed`, `Transfer`, `Arith`, `Godel`,
  `Universal`, `Packing` and `Undecidable`, and `Idioms`, which states the
  hand-written Brainfuck loops directly.
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
