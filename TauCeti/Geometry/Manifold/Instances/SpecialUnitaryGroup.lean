/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Lie.Subgroup.Transport
public import TauCeti.Geometry.Lie.Subgroup.SpecialUnitary
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Native special unitary and special orthogonal manifolds

For a finite index type and any `RCLike` scalar field, the original matrix special unitary
group has the atlas pulled back from its closed subgroup
of matrix units. Its inclusion is a smooth embedding, and its native Lie algebra is the real
algebra of trace-free skew-Hermitian matrices. Over the reals, the same construction supplies
Mathlib's special orthogonal group, whose native Lie algebra is Mathlib's `so`. Both comparisons
are characterized by the differential of the original inclusion.

Use `open scoped Matrix.Norms.Operator` and
`attribute [local instance] Matrix.linftyOpTopologicalSpace` for the matrix norm. This norm topology
coincides with the product topology on matrix entries for finite index types
(`Matrix.linftyOpTopologicalSpace_eq`).

## Main declarations

* `TauCeti.Lie.SpecialUnitaryGroupModel`: the real model space.
* `TauCeti.Lie.specialUnitaryEmbeddedData`: the chosen closed-subgroup structure.
* `TauCeti.Lie.closedSpecialUnitaryChartedSpace`, `TauCeti.Lie.closedSpecialUnitaryLieGroup`:
  its locally enabled closed-carrier structures.
* `TauCeti.Lie.specialUnitaryGroupChartedSpace`: the native atlas.
* `TauCeti.Lie.specialUnitaryGroup_isManifold`: the smooth manifold instance.
* `TauCeti.Lie.specialUnitaryGroup_lieGroup`: the smooth Lie-group instance.
* `TauCeti.Lie.isSmoothEmbedding_ofSpecialUnitaryGroup`: the canonical inclusion.
* `TauCeti.Lie.specialUnitaryGroupToGLSmoothHom`: the smooth inclusion and its `_apply` equation.
* `TauCeti.Lie.specialUnitaryGroupLieAlgebraEquiv`: trace-free skew-Hermitian coordinates.
* `TauCeti.Lie.coe_specialUnitaryGroupLieAlgebraEquiv_apply`: the inclusion differential.
* `TauCeti.Lie.specialOrthogonalGroupLieAlgebraEquiv`: the real specialization to `so`.
* `TauCeti.Lie.coe_specialOrthogonalGroupLieAlgebraEquiv_apply`: its inclusion differential.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), Proposition 3.24 (special unitary and orthogonal Lie algebras).

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12 (closed subgroups) and Proposition 7.11 (embedded Lie subgroups).
-/

public noncomputable section

open Matrix
open scoped Matrix Manifold ContDiff

namespace TauCeti.Lie

open scoped Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : Type*) [Fintype n] [DecidableEq n] (𝕜 : Type*) [RCLike 𝕜]

/-- The model of the native matrix special unitary group. -/
abbrev SpecialUnitaryGroupModel :=
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) (GLSpecialUnitary n 𝕜)).toSubmodule

/-- The canonical embedded structure on the special unitary subgroup of the units. -/
def specialUnitaryEmbeddedData :
    EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n 𝕜) (GLSpecialUnitary n 𝕜)
      (SpecialUnitaryGroupModel n 𝕜) :=
  EmbeddedLieSubgroupData.ofIsClosed (isClosed_GLSpecialUnitary n 𝕜)

/-- The closed-subgroup charts on the special unitary subgroup of the units. -/
local instance closedSpecialUnitaryChartedSpace :
    ChartedSpace (SpecialUnitaryGroupModel n 𝕜) (GLSpecialUnitary n 𝕜) :=
  (specialUnitaryEmbeddedData n 𝕜).chartedSpace

/-- The Lie-group structure on the special unitary subgroup in the closed-subgroup charts. -/
local instance closedSpecialUnitaryLieGroup :
    LieGroup 𝓘(ℝ, SpecialUnitaryGroupModel n 𝕜) ∞ (GLSpecialUnitary n 𝕜) :=
  (specialUnitaryEmbeddedData n 𝕜).lieGroup

/-- The native charts on the matrix special unitary group. -/
@[instance_reducible]
instance specialUnitaryGroupChartedSpace :
    ChartedSpace (SpecialUnitaryGroupModel n 𝕜) (Matrix.specialUnitaryGroup n 𝕜) :=
  (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜).toHomeomorph
    |>.pullbackChartedSpace (cM := closedSpecialUnitaryChartedSpace n 𝕜)

/-- The matrix special unitary group is a smooth real manifold. -/
instance specialUnitaryGroup_isManifold :
    IsManifold 𝓘(ℝ, SpecialUnitaryGroupModel n 𝕜) ∞ (Matrix.specialUnitaryGroup n 𝕜) :=
  (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜).toHomeomorph.pullback_isManifold
    (cM := closedSpecialUnitaryChartedSpace n 𝕜)
    (manifoldM := (closedSpecialUnitaryLieGroup n 𝕜).toContMDiffMul.toIsManifold)
    𝓘(ℝ, SpecialUnitaryGroupModel n 𝕜) ∞

/-- Mathlib's matrix special unitary group is a real Lie group in its original topology. -/
instance specialUnitaryGroup_lieGroup :
    LieGroup 𝓘(ℝ, SpecialUnitaryGroupModel n 𝕜) ∞ (Matrix.specialUnitaryGroup n 𝕜) :=
  (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜).lieGroup_pullbackChartedSpace
    (cB := closedSpecialUnitaryChartedSpace n 𝕜) (lieB := closedSpecialUnitaryLieGroup n 𝕜)
    (I := 𝓘(ℝ, SpecialUnitaryGroupModel n 𝕜)) (n := ∞)


end TauCeti.Lie

open TauCeti TauCeti.Lie
open scoped Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.Lie

variable (n : Type*) [Fintype n] [DecidableEq n] (𝕜 : Type*) [RCLike 𝕜]

local notation "E" => SpecialUnitaryGroupModel n 𝕜
local notation "S" => Matrix.specialUnitaryGroup n 𝕜
local notation "K" => GLSpecialUnitary n 𝕜

/-- The canonical real smooth inclusion into the group of matrix units. -/
def specialUnitaryGroupToGLSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, E) 𝓘(ℝ, Matrix n n 𝕜) ∞ S (GL n 𝕜) :=
  (specialUnitaryEmbeddedData n 𝕜).pullbackSmoothHom
    (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜)

/-- The smooth inclusion is the original matrix-to-units map. -/
@[simp]
theorem specialUnitaryGroupToGLSmoothHom_apply (A : S) :
    specialUnitaryGroupToGLSmoothHom n 𝕜 A = GLSpecialUnitary.ofSpecialUnitaryGroup n 𝕜 A := by
  exact ((specialUnitaryEmbeddedData n 𝕜).pullbackSmoothHom_apply
    ((GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜)) A).trans
    (GLSpecialUnitary.coe_specialUnitaryGroupContinuousMulEquiv n 𝕜 A)

/-- The inclusion of Mathlib's special unitary matrices into the units is a smooth embedding. -/
theorem isSmoothEmbedding_ofSpecialUnitaryGroup :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, SpecialUnitaryGroupModel n 𝕜)
      𝓘(ℝ, Matrix n n 𝕜) ∞ (GLSpecialUnitary.ofSpecialUnitaryGroup n 𝕜) := by
  have h := (specialUnitaryEmbeddedData n 𝕜).isSmoothEmbedding_pullbackSmoothHom
    (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜)
  have hinclusion : (specialUnitaryGroupToGLSmoothHom n 𝕜 : S → GL n 𝕜) =
      GLSpecialUnitary.ofSpecialUnitaryGroup n 𝕜 :=
    funext (specialUnitaryGroupToGLSmoothHom_apply n 𝕜)
  exact hinclusion ▸ h

private def coordinateEquiv :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) K ≃ₗ⁅ℝ⁆
      specialUnitaryMatrixLieAlgebra n 𝕜 :=
  (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).ofSubalgebras _ _
    unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_GLSpecialUnitary

/-- The real Lie algebra of the native special unitary group consists of trace-free
skew-Hermitian matrices. -/
def specialUnitaryGroupLieAlgebraEquiv :
    LeftInvariantDerivation 𝓘(ℝ, E) S ≃ₗ⁅ℝ⁆ specialUnitaryMatrixLieAlgebra n 𝕜 :=
  ((specialUnitaryEmbeddedData n 𝕜).pullbackLieEquiv
    (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜)).trans
      (coordinateEquiv n 𝕜)

private theorem coordinateEquiv_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) K) :
    (coordinateEquiv n 𝕜 X : Matrix n n 𝕜) = unitsLieAlgebraLieEquiv X := by
  rw [coordinateEquiv, LieEquiv.ofSubalgebras_apply]

/-- In matrix coordinates the native equivalence is the differential of the original inclusion. -/
@[simp↓]
theorem coe_specialUnitaryGroupLieAlgebraEquiv_apply (D : LeftInvariantDerivation 𝓘(ℝ, E) S) :
    (specialUnitaryGroupLieAlgebraEquiv n 𝕜 D : Matrix n n 𝕜) =
      unitsLieAlgebraLieEquiv (lieMap (specialUnitaryGroupToGLSmoothHom n 𝕜) D) := by
  exact (coordinateEquiv_apply n 𝕜
    ((specialUnitaryEmbeddedData n 𝕜).pullbackLieEquiv
      (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜) D)).trans
    (congrArg (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜))
      ((specialUnitaryEmbeddedData n 𝕜).coe_pullbackLieEquiv_apply
        (GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv n 𝕜) D))

end TauCeti.Lie

namespace TauCeti.Lie

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The real Lie algebra of the native special orthogonal group is Mathlib's `so`. -/
def specialOrthogonalGroupLieAlgebraEquiv :
    LeftInvariantDerivation 𝓘(ℝ, SpecialUnitaryGroupModel n ℝ) (Matrix.specialOrthogonalGroup n ℝ)
      ≃ₗ⁅ℝ⁆ LieAlgebra.Orthogonal.so n ℝ :=
  (specialUnitaryGroupLieAlgebraEquiv n ℝ).trans
    (LieEquiv.ofEq _ _ (by rw [specialUnitaryMatrixLieAlgebra_real_eq_so]))

/-- In matrix coordinates the real equivalence is the differential of the actual inclusion. -/
@[simp↓]
theorem coe_specialOrthogonalGroupLieAlgebraEquiv_apply
    (D : LeftInvariantDerivation 𝓘(ℝ, SpecialUnitaryGroupModel n ℝ)
      (Matrix.specialOrthogonalGroup n ℝ)) :
    (specialOrthogonalGroupLieAlgebraEquiv n D : Matrix n n ℝ) =
      unitsLieAlgebraLieEquiv (lieMap (specialUnitaryGroupToGLSmoothHom n ℝ) D) := by
  simpa only [specialOrthogonalGroupLieAlgebraEquiv, LieEquiv.trans_apply,
    LieEquiv.ofEq_apply] using
    coe_specialUnitaryGroupLieAlgebraEquiv_apply n ℝ D

end TauCeti.Lie
