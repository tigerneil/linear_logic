# Linear Logic in Lean 4

This project implements a formalization of linear logic in Lean 4, including:

- Core syntax for linear logic formulas
- Sequent calculus rules for inference
- Examples of theorems and proofs

## Overview

Linear logic, introduced by Jean-Yves Girard, is a resource-sensitive logic where assumptions must be used exactly once, unlike classical logic. This makes it well-suited for reasoning about computational resources, concurrency, and state.

Key features of linear logic formalized in this project:

- Multiplicative connectives: ⊗ (tensor), ⊸ (linear implication)
- Additive connectives: & (with), ⊕ (plus)
- Exponential modalities: ! (of course), ? (why not)
- Resource management rules based on consumption semantics

## Project Structure

- `LinearLogic/Basic.lean`: Core definitions and utilities
- `LinearLogic/Sequent.lean`: Sequent calculus implementation
- `LinearLogic/Examples.lean`: Example theorems and proofs
- `LinearLogic/Test.lean`: Test cases for the implementation
- `Main.lean`: Entry point for running the project

## Building and Running

The project uses Lake, Lean 4's build system:

```bash
# Build the project
lake build

# Run the main executable
lake exe linear_logic
```

## License

This project is available under the MIT License.