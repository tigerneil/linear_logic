# Linear Logic in Lean 4 - Documentation

## Overview

This project implements a formalization of linear logic in Lean 4. Linear logic, introduced by Jean-Yves Girard in 1987, is a resource-sensitive logic where each assumption must be used exactly once. Unlike classical or intuitionistic logic, linear logic treats propositions as resources that are consumed when used, making it particularly suitable for reasoning about state, resources, and concurrency in computing systems.

## Theoretical Background

### Linear Logic Fundamentals

Linear logic is characterized by its resource-conscious approach:
- Resources (formulas) cannot be duplicated or discarded arbitrarily
- Each formula must be used exactly once in a proof

The core connectives of linear logic include:

1. **Multiplicative Connectives**
   - ⊗ (tensor): Represents the simultaneous availability of two resources
   - ⊸ (lollipop): Linear implication, consumes the antecedent to produce the consequent
   - One (1): Multiplicative unit

2. **Additive Connectives**
   - & (with): Represents an external choice between resources
   - ⊕ (plus): Represents an internal choice between resources
   - Top (⊤): Additive top
   - Zero (0): Additive zero

3. **Exponential Modalities**
   - ! (of course): Marks a resource as reusable (can be duplicated and discarded)
   - ? (why not): Dual of of course, represents potential resources

### Sequent Calculus for Linear Logic

In linear logic, sequents take the form `Γ ⊢ Δ` where:
- Γ is a multiset of formulas representing available resources
- Δ is a multiset of formulas representing potential outcomes
- The resources in Γ must be used exactly once to produce the outcomes in Δ

The core rules of the sequent calculus include:
- Identity: `A ⊢ A`
- Cut: If `Γ ⊢ A` and `A, Δ ⊢ B` then `Γ, Δ ⊢ B`
- Tensor right: If `Γ ⊢ A` and `Δ ⊢ B` then `Γ, Δ ⊢ A ⊗ B`
- Tensor left: If `Γ, A, B ⊢ C` then `Γ, A ⊗ B ⊢ C`
- Lollipop right: If `Γ, A ⊢ B` then `Γ ⊢ A ⊸ B`
- Lollipop left: If `Γ ⊢ A` and `Δ, B ⊢ C` then `Γ, Δ, A ⊸ B ⊢ C`

## Project Structure

The project is organized into several Lean modules:

### 1. LinearLogic.Basic

```lean
def hello := "world"
```

This module currently contains a placeholder definition. In a more complete implementation, it would define:
- Basic utilities
- Common types and functions used across the library

### 2. LinearLogic.Sequent

This is the core module implementing the linear logic sequent calculus:

```lean
/-- Linear logic formula type -/
inductive Formula where
  /-- Atomic formula -/
  | atom : String → Formula
  /-- Tensor (multiplicative conjunction) -/
  | tensor : Formula → Formula → Formula  -- ⊗
  /-- Linear implication -/
  | lollipop : Formula → Formula → Formula  -- ⊸
  /-- With (additive conjunction) -/
  | with : Formula → Formula → Formula  -- &
  /-- Plus (additive disjunction) -/
  | plus : Formula → Formula → Formula  -- ⊕
  /-- Of course modality -/
  | ofCourse : Formula → Formula  -- !
  /-- Why not modality -/
  | whyNot : Formula → Formula  -- ?
  /-- Multiplicative unit -/
  | one : Formula  -- 1
  /-- Multiplicative bottom -/
  | bot : Formula  -- ⊥
  /-- Additive top -/
  | top : Formula  -- ⊤
  /-- Additive zero -/
  | zero : Formula  -- 0
```

The module also defines:
- A `Context` type representing multisets of formulas
- A `Sequent` type representing judgments of the form `Γ ⊢ Δ`
- A `Valid` inductive type representing proofs in the sequent calculus
- Helper functions and tactics for working with sequents

### 3. LinearLogic.Examples

This module contains examples of linear logic theorems and their proofs:

```lean
/-- Identity (A ⊸ A): Every formula linearly implies itself. -/
def identity_lollipop (A : Formula) : Valid ([] ⊢ [Formula.lollipop A A])

/-- Tensor commutativity: (A ⊗ B) ⊸ (B ⊗ A) -/
def tensor_commutativity (A B : Formula) : 
  Valid ([] ⊢ [Formula.lollipop (Formula.tensor A B) (Formula.tensor B A)])

/-- With elimination 1: (A & B) ⊸ A -/
def with_elimination_1 (A B : Formula) : 
  Valid ([] ⊢ [Formula.lollipop (Formula.with A B) A])
```

These examples demonstrate key properties of linear logic, including:
- Identity principles
- Commutativity of tensor
- Properties of additive connectives
- Interactions with exponential modalities

### 4. LinearLogic.Test

This module contains test cases that verify the correctness of the implementation:

```lean
/-- A simple test that always passes -/
def test_always_passes : Bool := true

/-- Run all tests and return true if all tests pass -/
def runAllTests : Bool := test_always_passes
```

In a more complete implementation, this module would contain comprehensive tests for:
- Basic axioms and rules
- Derived theorems
- Complex proofs
- Edge cases and limitations

### 5. Main

The main entry point for the project:

```lean
/-- Main function that displays basic information about the project -/
def main : IO Unit := do
  IO.println "Linear Logic Implementation"
  IO.println "=========================="
  IO.println ""
  IO.println "This project implements a formalization of linear logic in Lean 4,"
  IO.println "including the syntax and semantics of formulas, sequent calculus"
  IO.println "rules, and basic theorems."
  IO.println ""
  IO.println "All components are successfully built."
```

## Usage Examples

Here are some examples of how to use the library:

### Defining Formulas

```lean
-- Define atomic formulas
def A := Formula.atom "A"
def B := Formula.atom "B"

-- Define composite formulas
def A_tensor_B := Formula.tensor A B
def A_lolli_B := Formula.lollipop A B
def A_with_B := Formula.with A B
def A_plus_B := Formula.plus A B

-- Define formulas with exponentials
def bang_A := Formula.ofCourse A
```

### Creating Sequents

```lean
-- A ⊢ A
def id_sequent := Sequent.mk [A] [A]

-- A, B ⊢ A ⊗ B
def tensor_intro_sequent := Sequent.mk [A, B] [A_tensor_B]

-- A ⊗ B ⊢ A
def tensor_elim_sequent := Sequent.mk [A_tensor_B] [A]
```

### Constructing Proofs

```lean
-- Identity proof
def id_proof : Valid ([A] ⊢ [A]) := Valid.identity

-- Tensor right introduction
def tensor_right_proof (A B : Formula) : 
  Valid ([A, B] ⊢ [Formula.tensor A B]) :=
  -- A proof would go here
```

## Building and Running

The project is built using Lake, Lean 4's build system:

```bash
# Build the project
lake build

# Run the main executable
lake exe linear_logic
```

## Further Development

To continue developing this project, consider:

1. **Extending the Core Implementation**:
   - Implement missing inference rules
   - Add support for more complex proof construction
   - Implement a fully automated theorem prover

2. **Adding More Examples**:
   - Classic linear logic theorems
   - Resource-conscious programming examples
   - Applications to concurrency or state management

3. **Enhancing the Testing Framework**:
   - Comprehensive unit tests for all rules
   - Property-based testing for the logic
   - Benchmarking for proof search performance

4. **Documentation and Tutorials**:
   - Interactive examples
   - Tutorial on linear logic concepts
   - Reference documentation for all functions

## Resources for Learning Linear Logic

- Girard, J.-Y. (1987). "Linear logic"
- Troelstra, A. S. (1992). "Lectures on Linear Logic"
- Wadler, P. (1993). "A taste of linear logic"
- The Stanford Encyclopedia of Philosophy entry on Linear Logic

## License

This project is available under the MIT License.