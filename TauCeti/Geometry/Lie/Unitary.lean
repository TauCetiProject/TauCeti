/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SkewAdjoint.Star
public import TauCeti.Topology.Algebra.Star.Module
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import TauCeti.Geometry.Lie.Subgroup.Unitary
public import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# The Lie algebra of the native unitary and orthogonal groups

The Lie algebra of `unitary R`, with its original native atlas, is the skew-adjoint Lie
subalgebra of the finite-dimensional real star algebra `R`. The equivalence is the Lie
differential of the canonical inclusion `Unitary.toUnits`, expressed in algebra coordinates.
For matrix algebras this applies directly to `Matrix.unitaryGroup`; over the reals the
resulting orthogonal Lie algebra is Mathlib's `LieAlgebra.Orthogonal.so`.

Matrix results use the `L∞` operator norm. Enable `open scoped Matrix.Norms.Operator` and
`attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar`
when stating or using them. This topology agrees with the entrywise topology.

For complex matrices the target is the real Lie algebra of skew-Hermitian matrices.
For real matrices it is the skew-symmetric matrices, with the commutator bracket in both cases.

## Main declarations

* `Unitary.lieAlgebraLieEquiv`: the native unitary Lie algebra is the skew-adjoint Lie subalgebra.
* `Unitary.coe_lieAlgebraLieEquiv_apply`: the equivalence is the inclusion's Lie differential.
* `Matrix.orthogonalGroupLieAlgebraLieEquiv`: the native orthogonal Lie algebra is `so`.
* `Matrix.coe_orthogonalGroupLieAlgebraLieEquiv_apply`: its inclusion differential formula.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), Proposition 3.24 (unitary and orthogonal Lie algebras) and Theorem 3.28
  (the Lie differential of a homomorphism).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12 (closed subgroups).
-/

public section

open Set Manifold TauCeti TauCeti.Lie
open scoped Manifold ContDiff

noncomputable section

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance 100] LieRing.ofAssociativeRing

namespace Unitary

variable (R : Type*) [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]
  [StarRing R] [ContinuousStar R]

private local instance : CompleteSpace R := FiniteDimensional.complete ℝ R

local notation "K" => unitarySubgroup Rˣ
local notation "V" => LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, R)) K)

private def data : EmbeddedLieSubgroupData 𝓘(ℝ, R) K V :=
  EmbeddedLieSubgroupData.ofIsClosed (TauCeti.isClosed_unitarySubgroup_units R)

private local instance closedCharts : ChartedSpace V K := (data R).chartedSpace
private local instance closedLie : LieGroup 𝓘(ℝ, V) ∞ K := (data R).lieGroup

private def comparisonDiffeomorph :
    (unitary R) ≃ₘ^∞⟮Unitary.model R, 𝓘(ℝ, V)⟯ K where
  toEquiv := (TauCeti.unitarySubgroupUnitsHomeomorph R).symm.toEquiv
  contMDiff_toFun := by
    apply (data R).isSmoothEmbedding_subtypeVal.contMDiff_iff_comp.mpr
    exact (Unitary.contMDiff_toUnits (R := R)).congr fun u ↦ by
      simp only [Function.comp_apply, Homeomorph.coe_toEquiv,
        TauCeti.unitarySubgroupUnitsHomeomorph_symm_apply,
        TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply]
  contMDiff_invFun := by
    apply (isSmoothEmbedding_toUnits (R := R)).contMDiff_iff_comp.mpr
    exact (data R).contMDiff_subtypeVal.congr fun u ↦ by
      apply Units.ext
      simp only [Function.comp_apply, Homeomorph.coe_symm_toEquiv, Homeomorph.symm_symm,
        TauCeti.unitarySubgroupUnitsHomeomorph_apply,
        Unitary.val_toUnits_apply, unitarySubgroupUnitsEquiv_apply_coe]

private theorem comparisonDiffeomorph_coe_mulEquiv :
    ⇑(comparisonDiffeomorph R) = (unitarySubgroupUnitsEquiv : K ≃* unitary R).symm := by
  funext u
  exact TauCeti.unitarySubgroupUnitsHomeomorph_symm_apply u

private def comparisonSmoothHom :
    ContMDiffMonoidMorphism (Unitary.model R) 𝓘(ℝ, V) ∞ (unitary R) K where
  toMonoidHom := (unitarySubgroupUnitsEquiv : K ≃* unitary R).symm.toMonoidHom
  contMDiff_toFun := (comparisonDiffeomorph R).contMDiff.congr fun u ↦
    congrFun (comparisonDiffeomorph_coe_mulEquiv R).symm u

-- Rewrite the map explicitly below: the smooth-homomorphism wrapper does not reduce
-- inside the imported, opaque local-diffeomorphism predicate.
private theorem comparison_coe :
    ⇑(comparisonDiffeomorph R) = comparisonSmoothHom R := by
  funext u
  exact congrFun (comparisonDiffeomorph_coe_mulEquiv R) u

-- The two atlases give the same smooth maps because both inclusions into the units
-- are smooth embeddings. Their comparison therefore induces a canonical Lie equivalence.
private def nativeToClosedLieEquiv :
    LeftInvariantDerivation (Unitary.model R) (unitary R) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, V) K :=
  lieEquivOfIsLocalDiffeomorphAt (comparisonSmoothHom R) (by
    rw [← comparison_coe]
    exact (comparisonDiffeomorph R).isLocalDiffeomorph 1)

attribute [local instance] StarModule.real_of_continuousStar

private def skewCoordinateEquiv :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, R)) K ≃ₗ⁅ℝ⁆ skewAdjoint.lieSubalgebra ℝ R :=
  (unitsLieAlgebraLieEquiv (R := R)).ofSubalgebras _ _
    (unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_unitarySubgroup (R := R))

/-- The Lie algebra of the native unitary group is the skew-adjoint Lie subalgebra. -/
def lieAlgebraLieEquiv :
    LeftInvariantDerivation (Unitary.model R) (unitary R) ≃ₗ⁅ℝ⁆ skewAdjoint.lieSubalgebra ℝ R :=
  (nativeToClosedLieEquiv R).trans
    ((data R).lieEquivLieSubalgebraOfSubgroup.trans (skewCoordinateEquiv R))

private theorem comparison_comp_inclusion :
    (data R).subtypeVal.comp (comparisonSmoothHom R) = toUnitsSmoothHom (R := R) := by
  apply DFunLike.ext
  intro u
  rw [ContMDiffMonoidMorphism.coe_comp, Function.comp_apply, (data R).subtypeVal_apply]
  rw [toUnitsSmoothHom_apply]
  exact TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply u

private theorem skewCoordinateEquiv_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, R)) K) :
    (skewCoordinateEquiv R X : R) = unitsLieAlgebraLieEquiv (R := R) X :=
  (unitsLieAlgebraLieEquiv (R := R)).ofSubalgebras_apply _ _
    (unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_unitarySubgroup (R := R)) X

/-- In algebra coordinates, the native unitary Lie equivalence is the differential of
`Unitary.toUnitsSmoothHom`. -/
@[simp]
theorem coe_lieAlgebraLieEquiv_apply
    (D : LeftInvariantDerivation (Unitary.model R) (unitary R)) :
    (lieAlgebraLieEquiv R D : R) =
      unitsLieAlgebraLieEquiv (R := R) (lieMap (toUnitsSmoothHom (R := R)) D) := by
  simp only [lieAlgebraLieEquiv, LieEquiv.trans_apply]
  rw [skewCoordinateEquiv_apply, (data R).lieEquivLieSubalgebraOfSubgroup_apply,
    (data R).lieMapSubtypeVal_apply]
  have hnative : nativeToClosedLieEquiv R D = lieMap (comparisonSmoothHom R) D := by
    exact lieEquivOfIsLocalDiffeomorphAt_apply (comparisonSmoothHom R) _ D
  rw [hnative]
  have hcomp := DFunLike.congr_fun
    (lieMap_comp (comparisonSmoothHom R) (data R).subtypeVal) D
  rw [comparison_comp_inclusion] at hcomp
  exact congrArg (unitsLieAlgebraLieEquiv (R := R)) hcomp.symm

end Unitary

namespace Matrix

open scoped Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The Lie algebra of the native real orthogonal group is Mathlib's orthogonal Lie algebra.

Use the `L∞` operator norm: enable `Matrix.Norms.Operator` and the local instances
`Matrix.linftyOpTopologicalSpace` and `Matrix.linftyOpContinuousStar`. -/
def orthogonalGroupLieAlgebraLieEquiv :
    LeftInvariantDerivation (Unitary.model (Matrix n n ℝ)) (orthogonalGroup n ℝ) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so n ℝ :=
  (Unitary.lieAlgebraLieEquiv (Matrix n n ℝ)).trans
    (LieEquiv.ofEq _ _ (congrArg SetLike.coe (skewAdjoint_lieSubalgebra_eq_so (n := n))))

/-- The real orthogonal Lie equivalence is the differential of the original inclusion
into the general linear group, expressed in matrix coordinates. -/
@[simp]
theorem coe_orthogonalGroupLieAlgebraLieEquiv_apply
    (D : LeftInvariantDerivation (Unitary.model (Matrix n n ℝ)) (orthogonalGroup n ℝ)) :
    (orthogonalGroupLieAlgebraLieEquiv n D : Matrix n n ℝ) =
      unitsLieAlgebraLieEquiv (R := Matrix n n ℝ)
        (lieMap (Unitary.toUnitsSmoothHom (R := Matrix n n ℝ)) D) := by
  simpa only [orthogonalGroupLieAlgebraLieEquiv, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
    using Unitary.coe_lieAlgebraLieEquiv_apply (Matrix n n ℝ) D

end Matrix
