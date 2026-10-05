/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of the algebra norm

The norm of a finite free algebra is continuous when the algebra carries the module topology
over a topological base ring. This applies to finite extensions of completed fields and supplies
the local continuity input for adelic norm maps.

The topology on the algebra is specified by `IsModuleTopology R S`; no nontriviality assumption
on the base ring is needed.
-/

public section

namespace TauCeti

/-- The norm of a finite free algebra with the module topology is continuous. -/
@[continuity, fun_prop]
theorem continuous_algebraNorm (R S : Type*) [CommRing R] [Ring S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsModuleTopology R S] : Continuous (Algebra.norm R : S → R) := by
  classical
  let b := Module.Free.chooseBasis R S
  -- Use Mathlib's `Algebra.norm_eq_matrix_det`: left multiplication is linear in
  -- the algebra element and the determinant is continuous.
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.leftMulMatrix b).toLinearMap).matrix_det.congr fun x ↦
      (Algebra.norm_eq_matrix_det b x).symm

/-- The norm of a finite-dimensional Hausdorff topological vector space carrying an algebra
structure over a complete nontrivially normed field is continuous. -/
@[continuity, fun_prop]
theorem continuous_algebraNorm_of_finiteDimensional (𝕜 E : Type*)
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Ring E] [Algebra 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [FiniteDimensional 𝕜 E] : Continuous (Algebra.norm 𝕜 : E → 𝕜) := by
  let := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := E)
  exact continuous_algebraNorm 𝕜 E

end TauCeti
