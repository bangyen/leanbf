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
(`body ++ [instr] ++ rest`). `RunsTo : (Program × State) → State → Prop` is
the reflexive-transitive closure of `step`, and a program halts exactly when
its instruction list is empty.

### The Minsky Machine Model (`LeanBF.Core.Minsky`)

A two-counter Minsky machine (`Minsky.State`) has a program counter `pc` and
two unbounded counters `c1`, `c2`. Instructions are `inc1`, `inc2`,
`jzdec1`, `jzdec2`, and `halt`; `step` reads the instruction at `pc` and
`RunsTo` is its reflexive-transitive closure. This is the model Brainfuck
will be shown to simulate.

### The Compiler (`LeanBF.Core.Compiler`)

`Compiler.compileInstr` translates a single Minsky instruction into a
Brainfuck block for a large dispatch loop. The layout convention is: cell 0
is the `running` flag, cell 1 holds `pc`, cells 2 and 3 hold `c1` and `c2`,
and auxiliary cells start at cell 4. `movePtr` and `copyCell` generate the
pointer movement and cell-copy blocks.

> [!WARNING]
> The compiler is a work in progress: the `jzdec1` block is a placeholder and
> `jzdec2` is unimplemented. The completeness proof (Roadmap) cannot begin
> until these produce a complete dispatch loop.

## The Theory Layer

Theorems are kept separate from definitions (`LeanBF/Theory`), mirroring the
project convention that `Core` files contain only definitions.

- `Theory/Completeness.lean`: `Simulates` (a Brainfuck state that simulates
  a Minsky state — pointer at cell `0`, `tape 1 = pc`, `tape 2 = c1`,
  `tape 3 = c2`, `tape 0 = 1` for running) and the statement of the project's
  central goal, `turingCompleteness`. The statement is recorded as a
  conjecture, not a theorem: the run-level simulation argument that would
  witness it is open work (see the Roadmap).

## Example Programs

`LeanBF/Examples` holds example programs as `Program` data. `HelloWorld` is
the classic `++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.`
`+++++++..+++.` `>>.<-.<.` `+++.` `------.` `--------.` `>>+.>++.` program
together with its initial state.

> [!NOTE]
> Unlike the verified examples in the sibling LeanFunge project, the example
> programs here are data only: their run behavior is not yet `decide`-checked
> against `step`/`RunsTo`.

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
