/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.SpecialLinearGroup
public import TauCeti.Geometry.Lie.Subgroup.SpecialLinear
public import TauCeti.Geometry.Lie.Functor
import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Geometry.Lie.AutomaticSmoothness

/-!
# The Lie algebra of the native special linear group

The real Lie algebra of `Matrix.SpecialLinearGroup n 𝕜`, for an `RCLike` field `𝕜`, is
Mathlib's trace-zero algebra `LieAlgebra.SpecialLinear.sl n 𝕜` with scalars restricted to `ℝ`.
The group retains its native analytic charts and subspace topology. Its coordinate equivalence
is characterized by the real Lie differential of the original inclusion into the general linear
group.

The target uses the canonical `RestrictScalars` type synonym. For `𝕜 = ℂ`, this is the
underlying real Lie algebra of the complex trace-zero algebra. The empty and singleton
index types give trivial groups.

Matrix statements use the `L∞` operator norm. Enable `open scoped Matrix.Norms.Operator` and
`attribute [local instance] Matrix.linftyOpTopologicalSpace` when using them.

## Main declarations

* `Matrix.SpecialLinearGroup.toGLRealSmoothHom`: the real smooth inclusion into the general
  linear group.
* `Matrix.SpecialLinearGroup.toGLRealSmoothHom_apply`: the inclusion on group elements.
* `Matrix.SpecialLinearGroup.lieAlgebraLieEquiv`: the real Lie algebra is the trace-zero algebra.
* `Matrix.SpecialLinearGroup.coe_lieAlgebraLieEquiv_apply`: the inclusion differential formula.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222
  (2015), Proposition 3.23 (the special linear Lie algebra) and Theorem 3.28
  (the Lie differential of a homomorphism).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 20.12 (closed subgroups).
-/

public section

open Set Manifold TauCeti TauCeti.Lie Matrix
open scoped Manifold ContDiff Matrix.Norms.Operator

noncomputable section

namespace Matrix.SpecialLinearGroup

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Matrix.linftyOpTopologicalSpace

variable (n : Type*) [Fintype n] [DecidableEq n] (𝕜 : Type*) [RCLike 𝕜]

local notation "E" => Model n 𝕜
local notation "S" => SpecialLinearGroup n 𝕜

/-- The real smooth inclusion of the native special linear group into the general linear group. -/
def toGLRealSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, E) 𝓘(ℝ, Matrix n n 𝕜) ∞ S (GL n 𝕜) :=
  ContinuousMonoidHom.toContMDiffMonoidMorphism 𝓘(ℝ, E) 𝓘(ℝ, Matrix n n 𝕜)
    ⟨(toGL : S →* GL n 𝕜), continuous_toGL⟩

/-- The real smooth inclusion is the original `SpecialLinearGroup.toGL`. -/
@[simp]
theorem toGLRealSmoothHom_apply (A : S) : toGLRealSmoothHom n 𝕜 A = toGL A := by
  rw [toGLRealSmoothHom, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
  -- The continuous wrapper retains its `toMonoidHom` field.
  rfl

local notation "K" => MonoidHom.range (toGL : S →* GL n 𝕜)
local notation "V" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) K)

private def closedData : EmbeddedLieSubgroupData 𝓘(ℝ, Matrix n n 𝕜) K V :=
  EmbeddedLieSubgroupData.ofIsClosed isClosed_range_toGL

private local instance : ChartedSpace V K := (closedData n 𝕜).chartedSpace
private local instance : LieGroup 𝓘(ℝ, V) ∞ K := (closedData n 𝕜).lieGroup

private def comparisonMulEquiv : S ≃* K :=
  MonoidHom.ofInjective toGL_injective

@[fun_prop]
private theorem continuous_comparison : Continuous (comparisonMulEquiv n 𝕜) := by
  apply Topology.IsEmbedding.subtypeVal.continuous_iff.mpr
  exact continuous_toGL.congr fun A ↦ (MonoidHom.ofInjective_apply toGL_injective).symm

@[fun_prop]
private theorem continuous_comparison_symm : Continuous (comparisonMulEquiv n 𝕜).symm := by
  apply isEmbedding_toGL.continuous_iff.mpr
  exact continuous_subtype_val.congr fun A ↦
    (MonoidHom.apply_ofInjective_symm toGL_injective A).symm

private def comparisonDiffeomorph : S ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, V)⟯ K where
  toEquiv := (comparisonMulEquiv n 𝕜).toEquiv
  contMDiff_toFun := contMDiff_of_continuous_monoidHom
    (comparisonMulEquiv n 𝕜) (continuous_comparison n 𝕜)
  contMDiff_invFun := contMDiff_of_continuous_monoidHom
    (comparisonMulEquiv n 𝕜).symm (continuous_comparison_symm n 𝕜)

private def comparisonSmoothHom :
    ContMDiffMonoidMorphism 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ S K :=
  ContinuousMonoidHom.toContMDiffMonoidMorphism 𝓘(ℝ, E) 𝓘(ℝ, V)
    ⟨(comparisonMulEquiv n 𝕜).toMonoidHom, continuous_comparison n 𝕜⟩

private def nativeToClosedLieEquiv :
    LeftInvariantDerivation 𝓘(ℝ, E) S ≃ₗ⁅ℝ⁆ LeftInvariantDerivation 𝓘(ℝ, V) K :=
  lieEquivOfIsLocalDiffeomorphAt (comparisonSmoothHom n 𝕜)
    (by
      rw [comparisonSmoothHom, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
      exact (comparisonDiffeomorph n 𝕜).isLocalDiffeomorph 1)

private def slInclusionEquiv :
    RestrictScalars ℝ 𝕜 (LieAlgebra.SpecialLinear.sl n 𝕜) ≃ₗ⁅ℝ⁆
      ((LieAlgebra.SpecialLinear.sl n 𝕜).restrictScalarsIncl ℝ).range :=
  LieEquiv.ofInjective _ ((LieAlgebra.SpecialLinear.sl n 𝕜).restrictScalarsIncl_injective ℝ)

private def slCoordinateEquiv :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) K ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ 𝕜 (LieAlgebra.SpecialLinear.sl n 𝕜) :=
  ((unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).ofSubalgebras _ _
    (unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_range_toGL (n := n) (𝕂 := 𝕜))).trans
      (slInclusionEquiv n 𝕜).symm

/-- The real Lie algebra of the native special linear group is the underlying real
Lie algebra of Mathlib's trace-zero matrices. -/
def lieAlgebraLieEquiv :
    LeftInvariantDerivation 𝓘(ℝ, E) S ≃ₗ⁅ℝ⁆
      RestrictScalars ℝ 𝕜 (LieAlgebra.SpecialLinear.sl n 𝕜) :=
  (nativeToClosedLieEquiv n 𝕜).trans
    ((closedData n 𝕜).lieEquivLieSubalgebraOfSubgroup.trans (slCoordinateEquiv n 𝕜))

private theorem comparison_comp_inclusion :
    (closedData n 𝕜).subtypeVal.comp (comparisonSmoothHom n 𝕜) =
      toGLRealSmoothHom n 𝕜 := by
  apply DFunLike.ext
  intro A
  rw [ContMDiffMonoidMorphism.coe_comp, Function.comp_apply,
    (closedData n 𝕜).subtypeVal_apply, toGLRealSmoothHom_apply]
  rw [comparisonSmoothHom, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
  exact MonoidHom.ofInjective_apply toGL_injective

private theorem slCoordinateEquiv_apply
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n 𝕜)) K) :
    (RestrictScalars.addEquiv ℝ 𝕜 (LieAlgebra.SpecialLinear.sl n 𝕜)
      (slCoordinateEquiv n 𝕜 X) : Matrix n n 𝕜) = unitsLieAlgebraLieEquiv X := by
  have h := congrArg Subtype.val ((slInclusionEquiv n 𝕜).apply_symm_apply
    ((unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)).ofSubalgebras _ _
      (unitsLieAlgebraLieEquiv_map_lieSubalgebraOfSubgroup_range_toGL
        (n := n) (𝕂 := 𝕜)) X))
  simpa only [slCoordinateEquiv, LieEquiv.trans_apply, slInclusionEquiv,
    LieEquiv.ofInjective_apply, LieSubalgebra.restrictScalarsIncl_apply,
    LieEquiv.ofSubalgebras_apply] using h

/-- In matrix coordinates, the native special linear Lie equivalence is the real
differential of the original inclusion into the general linear group. -/
@[simp]
theorem coe_lieAlgebraLieEquiv_apply (D : LeftInvariantDerivation 𝓘(ℝ, E) S) :
    (RestrictScalars.addEquiv ℝ 𝕜 (LieAlgebra.SpecialLinear.sl n 𝕜)
      (lieAlgebraLieEquiv n 𝕜 D) : Matrix n n 𝕜) =
      unitsLieAlgebraLieEquiv (lieMap (toGLRealSmoothHom n 𝕜) D) := by
  simp only [lieAlgebraLieEquiv, LieEquiv.trans_apply]
  rw [slCoordinateEquiv_apply, (closedData n 𝕜).lieEquivLieSubalgebraOfSubgroup_apply,
    (closedData n 𝕜).lieMapSubtypeVal_apply]
  have hnative : nativeToClosedLieEquiv n 𝕜 D = lieMap (comparisonSmoothHom n 𝕜) D :=
    lieEquivOfIsLocalDiffeomorphAt_apply (comparisonSmoothHom n 𝕜) _ D
  rw [hnative]
  have hcomp := DFunLike.congr_fun
    (lieMap_comp (comparisonSmoothHom n 𝕜) (closedData n 𝕜).subtypeVal) D
  rw [comparison_comp_inclusion] at hcomp
  exact congrArg (unitsLieAlgebraLieEquiv (R := Matrix n n 𝕜)) hcomp.symm

end Matrix.SpecialLinearGroup
