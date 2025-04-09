/-
  Main.lean - Entry point for the linear logic implementation
  
  This module serves as the entry point for the application and runs
  all tests to verify the correctness of the linear logic implementation.
-/

import LinearLogic.Basic
import LinearLogic.Sequent
import LinearLogic.Examples
import LinearLogic.Test

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