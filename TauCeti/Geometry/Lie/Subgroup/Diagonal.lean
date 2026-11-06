/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Diagonal

/-!
# The positive diagonal group as a real Lie group

The positive real diagonal matrices carry the closed-subgroup smooth structure for their
subspace topology in the general linear group. Their model is the Lie subalgebra of the
ambient real general linear group, and their inclusion is smooth with injective differential.
These structures are available independently of the Iwasawa decomposition.

## Main declarations

* `TauCeti.Lie.posDiagonalEmbeddedLieSubgroupData`: the native closed-subgroup data.
* `TauCeti.Lie.posDiagonalChartedSpace`, `posDiagonalLieGroup`: the native closed-subgroup
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

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "AM" => LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup
  (I := 𝓘(ℝ, Matrix n n ℝ)) (posDiagonalSubgroup n ℝ))

-- The closedness instance uses entrywise matrix topology; the native Lie charts use the
-- operator-norm topology. Instance search cannot cross these presentations, while checking
-- the named proof against an explicit expected `IsClosed` type permits that conversion.
/-- The native closed-subgroup data of the positive real diagonal group. -/
def posDiagonalEmbeddedLieSubgroupData :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n ℝ) (posDiagonalSubgroup n ℝ)
      (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℝ))
      (posDiagonalSubgroup n ℝ)).toSubmodule :=
  EmbeddedLieSubgroupData.ofIsClosed (I := 𝓘(ℝ, Matrix n n ℝ))
    (G := GL n ℝ) (K := posDiagonalSubgroup n ℝ)
    (show IsClosed (posDiagonalSubgroup n ℝ : Set (GL n ℝ)) from
      isClosed_posDiagonalSubgroup n ℝ)

variable (n) in
/-- The closed-subgroup charts on the positive real diagonal matrices. -/
instance posDiagonalChartedSpace : ChartedSpace AM (posDiagonalSubgroup n ℝ) :=
  (posDiagonalEmbeddedLieSubgroupData (n := n)).chartedSpace

variable (n) in
/-- The real Lie-group structure on the positive diagonal matrices. -/
instance posDiagonalLieGroup : LieGroup 𝓘(ℝ, AM) ∞ (posDiagonalSubgroup n ℝ) :=
  (posDiagonalEmbeddedLieSubgroupData (n := n)).lieGroup

end TauCeti.Lie
