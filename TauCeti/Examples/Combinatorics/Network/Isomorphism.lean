/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Isomorphism.Residual
public import Mathlib.Logic.Equiv.Bool
import Mathlib.Algebra.Order.Group.Int

/-!
# Relabelling a signed residual network

There are two parallel arrows for every ordered pair of Boolean vertices, including loops.
Relabel both vertices and parallel arrows by Boolean negation. The lower bounds are negative,
and one of the two parallel arrows is saturated. Residual transport keeps the forward/reverse
tags distinct and commutes with a canonical adjustment to zero.
-/

public section

namespace TauCeti.Examples.ResidualIsomorphism

/-- A network with two arrows per ordered pair and signed bounds. Exposed so its arrow types
compute as `Bool` in the relabelling and residual examples. -/
@[expose, reducible]
def network : Network ℤ Bool where
  Hom _ _ := Bool
  lower := fun {_ _} _ ↦ -2
  upper := fun {_ _} _ ↦ 3
  lower_le_upper := fun {_ _} _ ↦ by decide

/-- Exchange the vertices and exchange the parallel-arrow identities simultaneously. -/
def relabel : network.Iso network where
  vertexEquiv := Equiv.boolNot
  homEquiv _ _ := Equiv.boolNot
  map_lower _ := rfl
  map_upper _ := rfl

/-- Each false-labelled arrow is saturated; each true-labelled arrow carries negative flow. -/
def assignment : network.Assignment ℤ := fun {_ _} (a : Bool) ↦ if a then -1 else 3

/-- The assignment respects both signed bounds. -/
theorem assignment_feasible : assignment ∈ Set.Icc network.lower network.upper := by
  constructor <;> intro x y a <;> cases a <;> norm_num [network, assignment]

-- The forward and reverse residual copies of a saturated loop remain different.
example : (relabel.residual assignment assignment_feasible).homEquiv false false
    (Sum.inl false) = Sum.inl true := by
  simp [relabel]

example : (relabel.residual assignment assignment_feasible).homEquiv false false
    (Sum.inr false) = Sum.inr true := by
  simp [relabel]

example : (network.residual assignment assignment_feasible).upper
    (x := false) (y := false) (Sum.inl false) = 0 := by
  norm_num [network, assignment]

example : (network.residual assignment assignment_feasible).upper
    (x := false) (y := false) (Sum.inr false) = 5 := by
  norm_num [network, assignment]

-- Zero lies within the original signed bounds, and the residual difference reaches it
-- before or after relabelling.
example : relabel.assignmentEquiv ℤ
    (residualUpdate assignment (residualDifference assignment 0)) =
    residualUpdate (relabel.assignmentEquiv ℤ assignment)
      ((relabel.residual assignment assignment_feasible).assignmentEquiv ℤ
        (residualDifference assignment 0)) :=
  relabel.assignmentEquiv_residualUpdate assignment assignment_feasible assignment _

example :
    (relabel.residual assignment assignment_feasible).assignmentEquiv ℤ
      (residualDifference assignment 0) ∈
        Set.Icc (network.residual (relabel.assignmentEquiv ℤ assignment)
          ((relabel.assignmentEquiv_mem_Icc_iff assignment).2 assignment_feasible)).lower
          (network.residual (relabel.assignmentEquiv ℤ assignment)
            ((relabel.assignmentEquiv_mem_Icc_iff assignment).2 assignment_feasible)).upper := by
  apply ((relabel.residual assignment assignment_feasible).assignmentEquiv_mem_Icc_iff _).2
  exact residualDifference_mem_Icc assignment_feasible
    ⟨fun _ _ _ ↦ by norm_num [network], fun _ _ _ ↦ by norm_num [network]⟩

end TauCeti.Examples.ResidualIsomorphism
