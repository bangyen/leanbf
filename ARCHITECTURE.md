# LeanBF Architecture

This document provides a technical overview of the `LeanBF` project's design patterns and core abstractions. It is intended for developers who wish to contribute to the formal verification of Brainfuck Turing completeness.

## Core Abstractions

### Machine State (`State`)
The state of the Brainfuck machine is represented by the `State` structure.
- **`ptr : Int`**: The current pointer location on the tape.
- **`tape : Int → Nat`**: An infinite tape mapping integer indices to natural numbers (cell values).
- **`input : List Nat`**: The input stream for the `,` instruction.
- **`output : List Nat`**: The output stream for the `.` instruction.

### Instruction Set (`Instruction`)
Brainfuck commands are modeled as an inductive type:
- **`inc_ptr` / `dec_ptr`**: `>` / `<`
- **`inc_val` / `dec_val`**: `+` / `-`
- **`loop body`**: `[` and `]` (recursive list of instructions)
- **`read` / `write`**: `,` / `.`

## Small-Step Semantics

The project uses small-step operational semantics defined in `LeanBF.Semantics`.
- **`step : Program × State → Option (Program × State)`**: Defines a single state transition.
- **`RunsTo : (Program × State) → State → Prop`**: The reflexive-transitive closure of the step relation, used to define termination and final states.

## Turing Completeness via Minsky Machines

To prove Brainfuck is Turing-complete, we implement a simulation of a 2-counter Minsky machine.

### Minsky Machine Model (`Minsky.State`)
A Minsky machine has:
- **`pc : Nat`**: Program counter.
- **`c1 : Nat`, `c2 : Nat`**: Two unbounded counters.

### Compiler (`LeanBF.Compiler`)
The compiler maps Minsky instructions to Brainfuck code blocks:
- **`INC c1`**: Translated to Brainfuck code that increments the value at the `c1` cell.
- **`JZDEC c1 target`**: Translated to a Brainfuck loop that checks if the `c1` cell is zero, jumping or decrementing accordingly.

## Project Structure

- **`LeanBF/Basic.lean`**: Foundation types and state management.
- **`LeanBF/Semantics.lean`**: Operational logic and execution rules.
- **`LeanBF/Minsky.lean`**: Formal definition of the target computation model.
- **`LeanBF/Compiler.lean`**: Translation routines.
- **`LeanBF/Completeness.lean`**: The core simulation theorems.

## Proof Automation

While most proofs are currently structural, future work includes custom tactics for simplifying Brainfuck pointer arithmetic and loop termination analysis.
