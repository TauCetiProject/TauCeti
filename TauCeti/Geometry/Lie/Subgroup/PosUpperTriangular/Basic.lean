/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.UpperTriangular.Positive

/-!
# Positive upper-triangular matrices as a real Lie group

The upper-triangular matrices with positive real diagonal carry the native closed-subgroup
smooth structure on their subspace topology in the general linear group. This construction
works over real and complex normed fields, with arbitrary finite linearly ordered indices,
including the empty index type. Its model is the existing canonical Lie subalgebra of the
subgroup in the ambient general linear Lie algebra.

## Main definitions and instances

* `TauCeti.Lie.posUpperTriangularEmbeddedLieSubgroupData`: native closed-subgroup data.
* `TauCeti.Lie.posUpperTriangularChartedSpace`: the closed-subgroup charts.
* `TauCeti.Lie.posUpperTriangularLieGroup`: the smooth real Lie-group structure.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 20.12, p.523.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312, for the positive upper-triangular factor in matrix Iwasawa decomposition.
-/

public noncomputable section

open Matrix Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace TauCeti.Lie

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {𝕜 : Type*} [RCLike 𝕜]

local notation "AN" => posUpperTriangularGroup ι 𝕜
local notation "ANModel" => LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup
  (I := 𝓘(ℝ, Matrix ι ι 𝕜)) AN)

/-- Native embedded-subgroup data for the positive upper-triangular group. -/
def posUpperTriangularEmbeddedLieSubgroupData :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix ι ι 𝕜) AN ANModel :=
  EmbeddedLieSubgroupData.ofIsClosed (I := 𝓘(ℝ, Matrix ι ι 𝕜))
    (isClosed_posUpperTriangularGroup ι 𝕜)

/-- The native closed-subgroup charts on the positive upper-triangular group. -/
instance posUpperTriangularChartedSpace : ChartedSpace ANModel AN :=
  (posUpperTriangularEmbeddedLieSubgroupData (ι := ι) (𝕜 := 𝕜)).chartedSpace

/-- The positive upper-triangular group is a smooth real Lie group on its subspace topology. -/
instance posUpperTriangularLieGroup : LieGroup 𝓘(ℝ, ANModel) ∞ AN :=
  (posUpperTriangularEmbeddedLieSubgroupData (ι := ι) (𝕜 := 𝕜)).lieGroup

end TauCeti.Lie
