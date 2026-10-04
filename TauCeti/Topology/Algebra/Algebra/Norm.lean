/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Continuity of the algebra norm

The norm of a finite free algebra is continuous when the algebra carries the module topology
over a topological base ring. This applies to finite extensions of completed fields and supplies
the local continuity input for adelic norm maps.

The construction uses Mathlib's `Algebra.norm_eq_matrix_det`: left multiplication is linear in
the algebra element and the determinant is continuous.
-/

public section

namespace TauCeti

/-- The norm of a finite free algebra with the module topology is continuous. -/
@[continuity, fun_prop]
theorem continuous_algebraNorm (R S : Type*) [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S] : Continuous (Algebra.norm R : S → R) := by
  classical
  rcases subsingleton_or_nontrivial R with h | h
  · exact continuous_const.congr fun x ↦ @Subsingleton.elim R h 1 (Algebra.norm R x)
  · let := h
    let b := Module.finBasis R S
    exact (IsModuleTopology.continuous_of_linearMap
      (Algebra.leftMulMatrix b).toLinearMap).matrix_det.congr fun x ↦
        (Algebra.norm_eq_matrix_det b x).symm

end TauCeti
