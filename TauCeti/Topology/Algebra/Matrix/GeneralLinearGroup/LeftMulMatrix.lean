/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LeftMulMatrix
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of the left multiplication embedding of units

Let `S` be an algebra over a complete nontrivially normed field `R`, with a finite basis
`b : Module.Basis ι R S`, and give `S` a Hausdorff vector space topology. The left multiplication
embedding `TauCeti.unitsLeftMulMatrix b : Sˣ →* GL ι R` is continuous for the topologies of the
unit groups: the matrix of left multiplication by `x` and the one by `x⁻¹` are linear in `x`,
respectively `x⁻¹`, on a finite-dimensional space.

## Main results

* `TauCeti.continuous_unitsLeftMulMatrix`: the left multiplication embedding is continuous.
-/

public section

namespace TauCeti

/-- **The left multiplication embedding of units is continuous**: `x ↦ leftMulMatrix b x` from
`Sˣ` to `GL ι R`, for `S` with a finite basis over a complete nontrivially normed field. -/
@[fun_prop]
theorem continuous_unitsLeftMulMatrix {R S ι : Type*} [Fintype ι] [DecidableEq ι]
    [NontriviallyNormedField R] [CompleteSpace R] [Ring S] [Algebra R S] [TopologicalSpace S]
    [IsTopologicalAddGroup S] [ContinuousSMul R S] [T2Space S] (b : Module.Basis ι R S) :
    Continuous (unitsLeftMulMatrix b) := by
  have : FiniteDimensional R S := Module.Finite.of_basis b
  refine (Units.continuous_map (f := (Algebra.leftMulMatrix b).toRingHom.toMonoidHom)
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional).congr fun x => ?_
  ext : 1
  simp

end TauCeti
