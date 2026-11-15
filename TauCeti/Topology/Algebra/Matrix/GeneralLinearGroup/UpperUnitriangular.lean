/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# Upper-unitriangular matrices form a closed subgroup

Over a ring whose points are closed, upper-unitriangular matrices are a closed subset of the
general linear group. Their diagonal entries equal one and their entries below the diagonal
vanish. Continuity of ring operations is not required.

## Main results

* `TauCeti.isClosed_upperUnitriangularGroup`: the closedness instance.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312, for the upper-unitriangular factor of the matrix Iwasawa decomposition.
-/

public section

open Matrix

namespace TauCeti

variable (ι R : Type*) [Fintype ι] [LinearOrder ι] [Ring R] [TopologicalSpace R] [T1Space R]

/-- The upper-unitriangular matrices are closed in the general linear group. -/
instance isClosed_upperUnitriangularGroup :
    IsClosed (upperUnitriangularGroup ι R : Set (GL ι R)) := by
  have heq : (upperUnitriangularGroup ι R : Set (GL ι R)) =
      Units.val ⁻¹' ({M : Matrix ι ι R | ∀ i j, j < i → M i j = 0} ∩ {M | ∀ i, M i i = 1}) := by
    ext g
    exact (UpperUnitriangularGroup.mem_iff (g := g)).trans (Matrix.isUpperUnitriangular_def _)
  rw [heq]
  refine IsClosed.preimage Units.continuous_val (IsClosed.inter ?_ ?_)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      isClosed_singleton.preimage (continuous_id.matrix_elem i j)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦
      isClosed_singleton.preimage (continuous_id.matrix_elem i i)

end TauCeti
