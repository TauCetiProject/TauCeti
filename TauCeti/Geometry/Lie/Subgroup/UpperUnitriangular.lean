/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.UpperUnitriangular

/-!
# Upper-unitriangular matrices as a real Lie group

The upper-unitriangular matrices over a `RCLike` field carry the real closed-subgroup smooth
structure for their subspace topology. Their model is the Lie subalgebra of the ambient
general linear group, and their inclusion is smooth with injective differential.
These structures are available independently of the Iwasawa decomposition.

## Main declarations

* `TauCeti.Lie.upperUnitriangularEmbeddedLieSubgroupData`: the native closed-subgroup data.
* `TauCeti.Lie.upperUnitriangularChartedSpace`, `upperUnitriangularLieGroup`: the native
  closed-subgroup
  charts and real Lie-group structure.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312, for this subgroup's role in the matrix Iwasawa decomposition.
-/

public noncomputable section

open Matrix Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace

namespace TauCeti.Lie

variable {n 𝕜 : Type*} [Fintype n] [LinearOrder n] [RCLike 𝕜]

local notation "NM" => LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup
  (I := 𝓘(ℝ, Matrix n n 𝕜)) (upperUnitriangularGroup n 𝕜))

-- The closedness instance uses entrywise matrix topology; the native Lie charts use the
-- operator-norm topology. Instance search cannot cross these presentations, while checking
-- the named proof against an explicit expected `IsClosed` type permits that conversion.
/-- The native closed-subgroup data of the upper-unitriangular group. -/
def upperUnitriangularEmbeddedLieSubgroupData :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n 𝕜) (upperUnitriangularGroup n 𝕜)
      (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜))
      (upperUnitriangularGroup n 𝕜)).toSubmodule :=
  EmbeddedLieSubgroupData.ofIsClosed (I := 𝓘(ℝ, Matrix n n 𝕜))
    (G := GL n 𝕜) (K := upperUnitriangularGroup n 𝕜)
    (show IsClosed (upperUnitriangularGroup n 𝕜 : Set (GL n 𝕜)) from
      isClosed_upperUnitriangularGroup n 𝕜)

variable (n 𝕜) in
/-- The closed-subgroup charts on the upper-unitriangular matrices. -/
instance upperUnitriangularChartedSpace :
    ChartedSpace NM (upperUnitriangularGroup n 𝕜) :=
  (upperUnitriangularEmbeddedLieSubgroupData (n := n) (𝕜 := 𝕜)).chartedSpace

variable (n 𝕜) in
/-- The real Lie-group structure on the upper-unitriangular matrices. -/
instance upperUnitriangularLieGroup : LieGroup 𝓘(ℝ, NM) ∞ (upperUnitriangularGroup n 𝕜) :=
  (upperUnitriangularEmbeddedLieSubgroupData (n := n) (𝕜 := 𝕜)).lieGroup

end TauCeti.Lie
