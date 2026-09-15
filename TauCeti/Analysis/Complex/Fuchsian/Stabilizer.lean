/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Point stabilizers in Fuchsian groups

Every point stabilizer in a discrete subgroup of `PSL(2, ℝ)` is finite by proper
discontinuity of the action on the upper half-plane, and is cyclic through its faithful
derivative character.

## Main results

* `Subgroup.isCyclic_stabilizer_of_discrete`: every point stabilizer in a discrete subgroup of
  `PSL(2, ℝ)` is cyclic.

## References

* [S. Katok, *Fuchsian Groups*, Chapter 2][katok1992]
-/

public section

open scoped MatrixGroups

noncomputable section

namespace Subgroup

open MulAction UpperHalfPlane

/-- Every point stabilizer in a discrete subgroup of `PSL(2, ℝ)` is finite cyclic. -/
theorem isCyclic_stabilizer_of_discrete (G : Subgroup PSL(2, ℝ)) [DiscreteTopology G]
    (tau : ℍ) : IsCyclic (stabilizer G tau) :=
  isCyclic_stabilizer G tau

end Subgroup
