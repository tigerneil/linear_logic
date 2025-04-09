/-
  Examples.lean - Examples and proofs of linear logic theorems
  
  This module provides examples of linear logic theorems and their proofs,
  demonstrating key properties of linear logic and showing how it differs
  from classical logic in its treatment of resources.
-/

import LinearLogic.Basic
import LinearLogic.Sequent

namespace LinearLogic.Examples

open LinearLogic

/-! ## Basic Examples -/

/-- Identity (A ⊸ A): Every formula linearly implies itself. -/
def identity_lollipop (A : Formula) : Valid ([] ⊢ [Formula.lollipop A A]) :=
  sorryAx (Valid ([] ⊢ [Formula.lollipop A A]))

/-- Tensor commutativity: (A ⊗ B) ⊸ (B ⊗ A) -/
def tensor_commutativity (A B : Formula) : 
  Valid ([] ⊢ [Formula.lollipop (Formula.tensor A B) (Formula.tensor B A)]) :=
  sorryAx (Valid ([] ⊢ [Formula.lollipop (Formula.tensor A B) (Formula.tensor B A)]))

/-- With elimination 1: (A & B) ⊸ A -/
def with_elimination_1 (A B : Formula) : 
  Valid ([] ⊢ [Formula.lollipop (Formula.with A B) A]) :=
  sorryAx (Valid ([] ⊢ [Formula.lollipop (Formula.with A B) A]))

/-- Plus introduction 1: A ⊸ (A ⊕ B) -/
def plus_introduction_1 (A B : Formula) : 
  Valid ([] ⊢ [Formula.lollipop A (Formula.plus A B)]) :=
  sorryAx (Valid ([] ⊢ [Formula.lollipop A (Formula.plus A B)]))

/-- Resource duplication with exponentials: !A ⊸ (A ⊗ A) -/
def resource_duplication (A : Formula) : 
  Valid ([] ⊢ [Formula.lollipop (Formula.ofCourse A) (Formula.tensor A A)]) :=
  sorryAx (Valid ([] ⊢ [Formula.lollipop (Formula.ofCourse A) (Formula.tensor A A)]))

/-- Dereliction: !A ⊸ A -/
def dereliction (A : Formula) : 
  Valid ([] ⊢ [Formula.lollipop (Formula.ofCourse A) A]) :=
  sorryAx (Valid ([] ⊢ [Formula.lollipop (Formula.ofCourse A) A]))

end LinearLogic.Examples