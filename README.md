# LeanBF

**Formal Verification of Brainfuck Turing Completeness in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanBF is a formalization of the Brainfuck programming language in [Lean 4](https://leanprover.github.io/). Its primary goal is to provide a rigorous proof of Brainfuck's Turing completeness by formally simulating a 2-counter Minsky machine.

## Motivation

Brainfuck is a minimalist, esoteric language with only eight commands. Despite its simplicity, it is Turing-complete. Proving this in a formal setting like Lean 4 demonstrates the power of formal verification to reason about computation models and the "minimal" requirements for universal computation.

## Architecture

For a detailed overview of the project's design patterns, including the Brainfuck state machine, small-step semantics, and the Minsky machine simulation, see [ARCHITECTURE.md](ARCHITECTURE.md).

## Key Components

- **[LeanBF/Basic.lean](LeanBF/Basic.lean)**: Definition of Brainfuck instructions and machine state (pointer, tape, I/O).
- **[LeanBF/Semantics.lean](LeanBF/Semantics.lean)**: Small-step operational semantics for Brainfuck programs.
- **[LeanBF/Minsky.lean](LeanBF/Minsky.lean)**: Formalization of 2-counter Minsky Machines.
- **[LeanBF/Compiler.lean](LeanBF/Compiler.lean)**: Mapping from Minsky instructions to Brainfuck code.
- **[LeanBF/Completeness.lean](LeanBF/Completeness.lean)**: The formal simulation theorem and Turing completeness proof.

## Installation & Building

Make sure you have [elan](https://github.com/leanprover/elan) installed for Lean 4 version management.

```bash
git clone https://github.com/bangyen/leanbf.git
cd leanbf
lake exe cache get  # Downloads the pre-compiled Mathlib libraries
lake build
```

## Contributing
This repo uses standard Mathlib naming conventions. If you're a Lean 4 enthusiast interested in computability theory, feel free to submit PRs!

## Citation

If you use this work in your research, please cite:

```bibtex
@misc{pham_leanbf_2026,
  author = {Pham, Bangyen},
  title = {LeanBF: Formal Verification of Brainfuck Turing Completeness in Lean 4},
  year = {2026},
  url = {https://github.com/bangyen/leanbf}
}
```
