/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# Smooth scalar extension for matrix general linear groups

The entrywise inclusion of real matrices into matrices over a `RCLike` field induces a real
smooth map of general linear groups, for any finite matrix index type. Both groups carry
their native open-submanifold structures in the matrix algebras with the operator norm.

## Main results

* `Matrix.GeneralLinearGroup.contMDiff_map_real`: real smoothness of scalar extension.

## References

* Mathlib's `Geometry.Manifold.Instances.UnitsOfNormedAlgebra`, `Units.contMDiff_val` and the
  native open-submanifold structure on units of a complete normed algebra.
-/

public noncomputable section

open Matrix Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

-- Use the normed scalar instance's seminormed parent consistently in native matrix models.
attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Extending real matrix coefficients to a `RCLike` field is a real smooth map on `GL n`.
This holds for every regularity order, including analytic. -/
theorem contMDiff_map_real {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Matrix n n ℝ) 𝓘(ℝ, Matrix n n 𝕜) k
      (map (n := n) (algebraMap ℝ 𝕜)) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  let c : Matrix n n ℝ →L[ℝ] Matrix n n 𝕜 :=
    RCLike.ofRealCLM.toLinearMap.mapMatrix.toContinuousLinearMap
  exact c.contDiff.contMDiff.comp Units.contMDiff_val

end Matrix.GeneralLinearGroup
