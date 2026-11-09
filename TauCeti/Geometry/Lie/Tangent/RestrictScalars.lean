/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.Lie.BaseChange.ComplexStructure
public import TauCeti.Geometry.Lie.RestrictScalars
public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Tangent.Differential
public import TauCeti.Geometry.Lie.Tangent.LieEquiv
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
import TauCeti.Geometry.Lie.InvariantVectorField.Basic
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The underlying real Lie algebra of a complex Lie group

A complex Lie group becomes a real Lie group by restricting scalars in its shared atlas.
The complex tangent Lie algebra, with scalars restricted to `ℝ`, is canonically isomorphic
to the native tangent Lie algebra of that real Lie group. The equivalence is the fibre at
one of the existing tangent-bundle realification, and it commutes with differentials of
holomorphic homomorphisms and with the tangent adjoint actions.

The tangent comparison is defined for complete normed complex models and third-order group
operations. For finite-dimensional smooth complex Lie groups, it also compares the complex
tangent Lie algebra with scalars restricted to `ℝ` and the real left-invariant derivation
algebra. Multiplication by `Complex.I` induces a real-linear endomorphism of the latter.
It squares to minus the identity and commutes with the bracket in each argument.

Use `LieGroup.restrictScalars_self` to install the underlying real Lie-group structure locally;
this module's real Lie-group instance is local as well.

## Main definitions

* `TauCeti.Lie.realificationLieEquiv`: the real Lie equivalence between the native tangent
  Lie algebras of a complex Lie group and its underlying real Lie group.
* `TauCeti.Lie.realificationDerivationLieEquiv`: the corresponding equivalence with real
  left-invariant derivations for finite-dimensional smooth complex Lie groups.
* `TauCeti.Lie.realificationDerivationComplexStructure`: multiplication by `Complex.I`
  transported to real left-invariant derivations.

## Main results

* `TauCeti.Lie.realificationLieEquiv_apply` and
  `TauCeti.Lie.realificationLieEquiv_symm_apply`: agreement with the public fibre equivalence.
* `TauCeti.Lie.realificationLieEquiv_groupLieAlgebraMap`: naturality under differentials
  of homomorphisms differentiable at the identity.
* `TauCeti.Lie.realificationLieEquiv_tangentAd`: compatibility with the adjoint actions.
* `TauCeti.Lie.realificationDerivationLieEquiv_apply` and
  `TauCeti.Lie.realificationDerivationLieEquiv_symm_apply`: the derivation comparison
  and evaluation at the identity.
* `TauCeti.Lie.realificationComplexStructure`: the complex structure on the native real
  tangent Lie algebra, without finite-dimensionality assumptions.
* `TauCeti.Lie.realificationComplexStructure_apply` and
  `TauCeti.Lie.realificationComplexStructure_realificationLieEquiv`: its coordinate equations.
* `TauCeti.Lie.realificationComplexStructure_sq` and
  `TauCeti.Lie.realificationComplexStructure_apply_apply`: its square is minus the identity.
* `TauCeti.Lie.realificationComplexStructure_lie_left` and
  `TauCeti.Lie.realificationComplexStructure_lie_right`: compatibility with the tangent bracket.
* Evaluation at the identity intertwines the two complex structures:
  `leftInvariantDerivationLieEquivGroupLieAlgebra_realificationDerivationComplexStructure`.
* `TauCeti.Lie.realificationDerivationComplexStructure_apply`: the complex structure in
  complex tangent coordinates.
* `TauCeti.Lie.realificationDerivationComplexStructure_realificationDerivationLieEquiv`:
  compatibility with multiplication by `Complex.I` on the complex tangent algebra.
* `TauCeti.Lie.realificationDerivationComplexStructure_sq`: the induced endomorphism
  squares to minus the identity.
* `TauCeti.Lie.realificationDerivationComplexStructure_apply_apply`: pointwise reduction
  of two successive applications of the induced complex structure.
* `TauCeti.Lie.realificationDerivationComplexStructure_lie_left` and
  `TauCeti.Lie.realificationDerivationComplexStructure_lie_right`: complex bilinearity
  of the real derivation bracket.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer Monographs in
  Mathematics (2012), §15.1, Definition 15.1.1 and §15.2, Exercise 15.2.3, for complex Lie
  groups as real Lie groups with compatible complex Lie algebras.
* `Mathlib.Geometry.Manifold.GroupLieAlgebra`, for the bracket of invariant vector fields;
  `TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars`, for the underlying real derivative.
-/

public section

open scoped ContDiff Manifold Topology
open Filter

namespace TauCeti.Lie

open GroupLieAlgebra

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G]

-- Normalize the restricted self-model before using the fibre map in typeclass inference.
-- Self-model restriction preserves the underlying maps definitionally; the model equality
-- fixes the tag before instance inference. The resulting cast therefore acts as the identity.
private def realificationTangent (x : G) :
    RestrictScalars ℝ ℂ (TangentSpace 𝓘(ℂ, E) x) ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x := by
  have e := TangentSpace.restrictScalarsLinearEquiv ℝ (I := 𝓘(ℂ, E)) x
  rw [modelWithCornersSelf_restrictScalars] at e
  exact e

private theorem realificationTangent_apply (x : G)
    (v : RestrictScalars ℝ ℂ (TangentSpace 𝓘(ℂ, E) x)) :
    realificationTangent x v = (tangentSpaceCastModel 𝓘(ℝ, E) x).symm
      (tangentSpaceCastModel 𝓘(ℂ, E) x (RestrictScalars.addEquiv ℝ ℂ _ v)) := by
  -- The specialization changes only the model tag, preserving the fibre map.
  have h : realificationTangent x v =
      TangentSpace.restrictScalarsLinearEquiv ℝ (I := 𝓘(ℂ, E)) x v := rfl
  rw [TangentSpace.restrictScalarsLinearEquiv_apply] at h
  rw [modelWithCornersSelf_restrictScalars] at h
  exact h

private theorem realificationTangent_mfderiv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
    {f : G → N} {x : G} (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x)
    (v : RestrictScalars ℝ ℂ (TangentSpace 𝓘(ℂ, E) x)) :
    realificationTangent (f x) ((RestrictScalars.addEquiv ℝ ℂ _).symm
        (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x (RestrictScalars.addEquiv ℝ ℂ _ v))) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x (realificationTangent x v) := by
  have h := hf.mfderiv_restrictScalars_apply ℝ v
  rw [TangentSpace.restrictScalarsLinearEquiv_apply,
    TangentSpace.restrictScalarsLinearEquiv_apply] at h
  rw [modelWithCornersSelf_restrictScalars, modelWithCornersSelf_restrictScalars] at h
  simpa only [realificationTangent_apply] using h

private theorem realificationTangent_mvfderiv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : G → F} {x : G} (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) f x)
    (v : RestrictScalars ℝ ℂ (TangentSpace 𝓘(ℂ, E) x)) :
    mvfderiv 𝓘(ℝ, E) f x (realificationTangent x v) =
      mvfderiv 𝓘(ℂ, E) f x (RestrictScalars.addEquiv ℝ ℂ _ v) := by
  have h := congrArg (tangentSpaceCastModel 𝓘(ℝ, F) (f x))
    (realificationTangent_mfderiv hf v)
  simp only [realificationTangent_apply, AddEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply] at h
  simp only [mvfderiv, NormedSpace.fromTangentSpace, realificationTangent_apply]
  rw [ContinuousLinearMap.comp_apply]
  exact h.symm

section Tangent

variable [Group G] [LieGroup 𝓘(ℂ, E) 3 G]

/-- The underlying real Lie-group structure used locally in the tangent comparison. -/
local instance realificationLieGroup : LieGroup 𝓘(ℝ, E) 3 G :=
  LieGroup.restrictScalars_self ℝ (𝕜 := ℂ)

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

private theorem realificationTangent_mulInvariantVectorField
    (v : GroupLieAlgebra 𝓘(ℂ, E) G) (g : G) :
    realificationTangent g
        ((RestrictScalars.addEquiv ℝ ℂ _).symm (mulInvariantVectorField v g)) =
      mulInvariantVectorField (I := 𝓘(ℝ, E))
        (realificationTangent (1 : G)
          ((RestrictScalars.addEquiv ℝ ℂ _).symm v)) g := by
  have h := realificationTangent_mfderiv
    ((contMDiff_mul_left (I := 𝓘(ℂ, E)) (n := 3) (a := g)).mdifferentiableAt
      (by simp) (x := (1 : G))) ((RestrictScalars.addEquiv ℝ ℂ _).symm v)
  rw [mul_one] at h
  simp only [AddEquiv.apply_symm_apply] at h
  simp only [mulInvariantVectorField]
  exact h

variable [CompleteSpace E]

private theorem realificationTangent_lie (v w : GroupLieAlgebra 𝓘(ℂ, E) G) :
    realificationTangent (1 : G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm ⁅v, w⁆) =
      ⁅(realificationTangent (1 : G)
          ((RestrictScalars.addEquiv ℝ ℂ _).symm v) : GroupLieAlgebra 𝓘(ℝ, E) G),
        realificationTangent (1 : G)
          ((RestrictScalars.addEquiv ℝ ℂ _).symm w)⁆ := by
  rw [GroupLieAlgebra.bracket_def, GroupLieAlgebra.bracket_def]
  apply TauCeti.eq_mlieBracket_of_mvfderiv_extChartAt
    ((contMDiff_mulInvariantVectorField _).mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiff_mulInvariantVectorField _).mdifferentiable (by simp)).mdifferentiableAt
  have hchart : extChartAt 𝓘(ℝ, E) (1 : G) = extChartAt 𝓘(ℂ, E) (1 : G) := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      (ModelWithCorners.extChartAt_restrictScalars ℝ 𝓘(ℂ, E) (1 : G))
  let f : G → E := extChartAt 𝓘(ℂ, E) (1 : G)
  have hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) 2 f (1 : G) := contMDiffAt_extChartAt
  have hinner (u : GroupLieAlgebra 𝓘(ℂ, E) G) :
      MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E)
        (fun y ↦ mvfderiv 𝓘(ℂ, E) f y (mulInvariantVectorField u y)) (1 : G) := by
    exact ((hf.contMDiffAt_mvfderiv_apply (m := 1) (p :=
      ⟨1, mulInvariantVectorField u (1 : G)⟩) (by norm_num)).comp (1 : G)
      ((contMDiff_mulInvariantVectorField u).of_le (m := 1)
        (by simp)).contMDiffAt).mdifferentiableAt (by simp)
  have hnear (u : GroupLieAlgebra 𝓘(ℂ, E) G) :
      (fun y ↦ mvfderiv 𝓘(ℝ, E) f y
        (mulInvariantVectorField (I := 𝓘(ℝ, E))
          (realificationTangent (1 : G)
            ((RestrictScalars.addEquiv ℝ ℂ _).symm u)) y)) =ᶠ[𝓝 (1 : G)]
      (fun y ↦ mvfderiv 𝓘(ℂ, E) f y (mulInvariantVectorField u y)) := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, E)) (1 : G)] with y hy
    rw [← realificationTangent_mulInvariantVectorField]
    simpa only [AddEquiv.apply_symm_apply] using
      realificationTangent_mvfderiv (mdifferentiableAt_extChartAt (by
        simpa only [extChartAt_source] using hy))
          ((RestrictScalars.addEquiv ℝ ℂ _).symm (mulInvariantVectorField u y))
  rw [hchart]
  -- `f` is a local abbreviation, so expose it with `change`; this also identifies the
  -- model/tangent-space coercions in the bracket comparison.
  change mvfderiv 𝓘(ℝ, E) f (1 : G)
      (realificationTangent (1 : G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm (VectorField.mlieBracket 𝓘(ℂ, E)
          (mulInvariantVectorField v) (mulInvariantVectorField w) (1 : G)))) = _
  rw [realificationTangent_mvfderiv (hf.mdifferentiableAt (by simp)),
    (hnear w).mvfderiv_eq, (hnear v).mvfderiv_eq, mulInvariantVectorField_one,
    mulInvariantVectorField_one, realificationTangent_mvfderiv (hinner w),
    realificationTangent_mvfderiv (hinner v)]
  simpa only [AddEquiv.apply_symm_apply, mulInvariantVectorField_one] using
    (mvfderiv_mlieBracket hf (by simp)
      ((contMDiff_mulInvariantVectorField v).mdifferentiable (by simp)).mdifferentiableAt
      ((contMDiff_mulInvariantVectorField w).mdifferentiable (by simp)).mdifferentiableAt)

/-- The native tangent Lie algebra of a complex Lie group, with scalars restricted to `ℝ`,
is the Lie algebra of the underlying real Lie group. -/
def realificationLieEquiv :
    RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G) ≃ₗ⁅ℝ⁆ GroupLieAlgebra 𝓘(ℝ, E) G :=
  { toFun := realificationTangent (1 : G)
    invFun := (realificationTangent (1 : G)).symm
    left_inv := (realificationTangent (1 : G)).left_inv
    right_inv := (realificationTangent (1 : G)).right_inv
    map_add' := (realificationTangent (1 : G)).map_add
    map_smul' := (realificationTangent (1 : G)).map_smul
    map_lie' := by
      intro x y
      have h := realificationTangent_lie (E := E) (G := G)
        (RestrictScalars.addEquiv ℝ ℂ _ x) (RestrictScalars.addEquiv ℝ ℂ _ y)
      -- The restricted Lie ring has the original bracket on its additive carrier.
      have hb : (RestrictScalars.addEquiv ℝ ℂ _).symm
          ⁅RestrictScalars.addEquiv ℝ ℂ _ x, RestrictScalars.addEquiv ℝ ℂ _ y⁆ = ⁅x, y⁆ := rfl
      rw [hb] at h
      simpa only [AddEquiv.symm_apply_apply] using h }

/-- The real Lie equivalence is the public fibre equivalence at the identity. -/
@[simp]
theorem realificationLieEquiv_apply
    (x : RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
    realificationLieEquiv (E := E) (G := G) x =
      (tangentSpaceCastModel 𝓘(ℝ, E) (1 : G)).symm
        (tangentSpaceCastModel 𝓘(ℂ, E) (1 : G) (RestrictScalars.addEquiv ℝ ℂ _ x)) := by
  exact realificationTangent_apply (1 : G) x

/-- Inverse Lie-algebra realification is the inverse public fibre equivalence. -/
@[simp]
theorem realificationLieEquiv_symm_apply (x : GroupLieAlgebra 𝓘(ℝ, E) G) :
    (realificationLieEquiv (E := E) (G := G)).symm x =
      (RestrictScalars.addEquiv ℝ ℂ _).symm
        ((tangentSpaceCastModel 𝓘(ℂ, E) (1 : G)).symm
          (tangentSpaceCastModel 𝓘(ℝ, E) (1 : G) x)) := by
  apply (realificationLieEquiv (E := E) (G := G)).injective
  -- Normalize the Lie-homomorphism coercion used by the injectivity API.
  change realificationLieEquiv (E := E) (G := G)
      ((realificationLieEquiv (E := E) (G := G)).symm x) =
    realificationLieEquiv (E := E) (G := G)
      ((RestrictScalars.addEquiv ℝ ℂ _).symm
        ((tangentSpaceCastModel 𝓘(ℂ, E) (1 : G)).symm
          (tangentSpaceCastModel 𝓘(ℝ, E) (1 : G) x)))
  rw [LieEquiv.apply_symm_apply, realificationLieEquiv_apply]
  simp only [AddEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The realification equivalence intertwines the complex and real tangent adjoint actions. -/
theorem realificationLieEquiv_tangentAd (g : G) (x : GroupLieAlgebra 𝓘(ℂ, E) G) :
    realificationLieEquiv (E := E) (G := G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm (tangentAd (I := 𝓘(ℂ, E)) g x)) =
      TauCeti.Lie.tangentAd (I := 𝓘(ℝ, E)) g (realificationLieEquiv (E := E) (G := G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm x)) := by
  let _ : LieGroup 𝓘(ℂ, E) 1 G := LieGroup.of_le (n := 3) (by norm_num)
  let _ : LieGroup 𝓘(ℝ, E) 1 G := LieGroup.of_le (n := 3) (by norm_num)
  have hφ := (TauCeti.Lie.conjDiffeomorph (I := 𝓘(ℂ, E)) (n := 1) g).mdifferentiable
    one_ne_zero (1 : G)
  have h := realificationTangent_mfderiv hφ
    ((RestrictScalars.addEquiv ℝ ℂ _).symm x)
  rw [conjDiffeomorph_apply, mul_one, mul_inv_cancel] at h
  simp only [AddEquiv.apply_symm_apply] at h
  have heq : (TauCeti.Lie.conjDiffeomorph (I := 𝓘(ℝ, E)) (n := 1) g : G → G) =
      (TauCeti.Lie.conjDiffeomorph (I := 𝓘(ℂ, E)) (n := 1) g : G → G) := by
    funext y
    simp only [TauCeti.Lie.conjDiffeomorph_apply]
  have hR := DFunLike.congr_fun
    (mfderiv_congr (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (x := (1 : G)) heq)
    (realificationTangent (1 : G)
      ((RestrictScalars.addEquiv ℝ ℂ _).symm x))
  simp only [TauCeti.Lie.tangentAd_apply, TauCeti.Lie.adjointContinuousLinearMap_apply]
  rw [realificationLieEquiv_apply, realificationLieEquiv_apply]
  rw [realificationTangent_apply] at hR
  rw [realificationTangent_apply, realificationTangent_apply] at h
  exact h.trans hR.symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace F K] [LieGroup 𝓘(ℂ, F) 3 K]

/-- Realification commutes with the differential of a homomorphism differentiable over `ℂ`
at the identity. The source and target groups and models may have different universes. -/
theorem realificationLieEquiv_groupLieAlgebraMap (φ : G →* K)
    (hφ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) φ 1)
    (x : GroupLieAlgebra 𝓘(ℂ, E) G) :
    realificationLieEquiv (E := F) (G := K)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm
          (φ.groupLieAlgebraMap 𝓘(ℂ, E) 𝓘(ℂ, F) x)) =
      φ.groupLieAlgebraMap 𝓘(ℝ, E) 𝓘(ℝ, F) (realificationLieEquiv (E := E) (G := G)
          ((RestrictScalars.addEquiv ℝ ℂ _).symm x)) := by
  have h := realificationTangent_mfderiv hφ
    ((RestrictScalars.addEquiv ℝ ℂ _).symm x)
  rw [φ.map_one] at h
  simp only [AddEquiv.apply_symm_apply] at h
  rw [MonoidHom.groupLieAlgebraMap_apply, MonoidHom.groupLieAlgebraMap_apply,
    realificationLieEquiv_apply, realificationLieEquiv_apply]
  rw [realificationTangent_apply, realificationTangent_apply] at h
  exact h

/-- Multiplication by `Complex.I` transported to the real tangent Lie algebra
of a complex Lie group with complete model and third-order operations. -/
def realificationComplexStructure : Module.End ℝ (GroupLieAlgebra 𝓘(ℝ, E) G) :=
  (realificationLieEquiv (E := E) (G := G)).complexStructure

/-- The induced real endomorphism corresponds to multiplication by `Complex.I`. -/
theorem realificationComplexStructure_realificationLieEquiv
    (x : RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
    realificationComplexStructure (realificationLieEquiv (E := E) (G := G) x) =
      realificationLieEquiv (E := E) (G := G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm
          (Complex.I • RestrictScalars.addEquiv ℝ ℂ _ x)) := by
  exact (realificationLieEquiv (E := E) (G := G)).complexStructure_apply_image x

/-- The induced complex structure is multiplication by `Complex.I` in complex tangent
coordinates. -/
-- Keep the complex structure opaque to simp so its algebraic bracket laws are normal forms.
theorem realificationComplexStructure_apply (D : GroupLieAlgebra 𝓘(ℝ, E) G) :
    realificationComplexStructure D =
      realificationLieEquiv (E := E) (G := G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm
          (Complex.I • RestrictScalars.addEquiv ℝ ℂ _
            ((realificationLieEquiv (E := E) (G := G)).symm D))) := by
  exact (realificationLieEquiv (E := E) (G := G)).complexStructure_apply D

/-- The induced endomorphism of real tangent vectors squares to minus the identity. -/
@[simp]
theorem realificationComplexStructure_sq :
    (realificationComplexStructure (E := E) (G := G)) ^ 2 = -1 := by
  exact (realificationLieEquiv (E := E) (G := G)).complexStructure_sq

/-- Two applications of the induced complex structure negate a real tangent vector. -/
@[simp]
theorem realificationComplexStructure_apply_apply
    (D : GroupLieAlgebra 𝓘(ℝ, E) G) :
    realificationComplexStructure (realificationComplexStructure D) = -D := by
  exact (realificationLieEquiv (E := E) (G := G)).complexStructure_apply_apply D

/-- The complex structure commutes with the real tangent bracket in its first argument. -/
@[simp]
theorem realificationComplexStructure_lie_left (X Y : GroupLieAlgebra 𝓘(ℝ, E) G) :
    ⁅realificationComplexStructure (E := E) (G := G) X, Y⁆ =
      realificationComplexStructure (E := E) (G := G) ⁅X, Y⁆ := by
  exact (realificationLieEquiv (E := E) (G := G)).complexStructure_lie_left X Y

/-- The complex structure commutes with the real tangent bracket in its second argument. -/
@[simp]
theorem realificationComplexStructure_lie_right
    (X Y : GroupLieAlgebra 𝓘(ℝ, E) G) :
    ⁅X, realificationComplexStructure (E := E) (G := G) Y⁆ =
      realificationComplexStructure (E := E) (G := G) ⁅X, Y⁆ := by
  exact (realificationLieEquiv (E := E) (G := G)).complexStructure_lie_right X Y

end Tangent

section Derivation

variable [FiniteDimensional ℝ E] [Group G] [LieGroup 𝓘(ℂ, E) ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The underlying smooth real Lie-group structure used locally for real derivations. -/
local instance realificationSmoothLieGroup : LieGroup 𝓘(ℝ, E) ∞ G :=
  LieGroup.restrictScalars_self ℝ (𝕜 := ℂ)

/-- The complex tangent Lie algebra with scalars restricted to `ℝ` is the real
left-invariant derivation algebra of a finite-dimensional smooth complex Lie group. -/
def realificationDerivationLieEquiv :
    RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, E) G :=
  (TauCeti.Lie.realificationLieEquiv (E := E) (G := G)).trans
    (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))).symm

/-- Realification sends a complex tangent vector to its real invariant derivation. -/
@[simp]
theorem realificationDerivationLieEquiv_apply
    (x : RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
    realificationDerivationLieEquiv (E := E) (G := G) x =
      tangentToLeftInvariantDerivation (realificationLieEquiv (E := E) (G := G) x) := by
  rw [realificationDerivationLieEquiv, LieEquiv.trans_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply]

/-- The inverse real derivation comparison is evaluation at the identity followed by inverse
realification of the tangent vector. -/
@[simp]
theorem realificationDerivationLieEquiv_symm_apply (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    (realificationDerivationLieEquiv (E := E) (G := G)).symm D =
      (realificationLieEquiv (E := E) (G := G)).symm
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
          (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D) := by
  rfl

/-- Multiplication by `Complex.I` transported to the real left-invariant derivation algebra
of a finite-dimensional smooth complex Lie group. -/
def realificationDerivationComplexStructure : Module.End ℝ (LeftInvariantDerivation 𝓘(ℝ, E) G) :=
  (realificationDerivationLieEquiv (E := E) (G := G)).complexStructure

/-- The induced real endomorphism corresponds to multiplication by `Complex.I`. -/
theorem realificationDerivationComplexStructure_realificationDerivationLieEquiv
    (x : RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
    realificationDerivationComplexStructure (realificationDerivationLieEquiv (E := E) (G := G) x) =
      realificationDerivationLieEquiv (E := E) (G := G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm
          (Complex.I • RestrictScalars.addEquiv ℝ ℂ _ x)) := by
  exact (realificationDerivationLieEquiv (E := E) (G := G)).complexStructure_apply_image x

/-- Evaluation at the identity intertwines the derivation and tangent complex structures. -/
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_realificationDerivationComplexStructure
    (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
        (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))
        (realificationDerivationComplexStructure D) =
      realificationComplexStructure
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
          (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D) := by
  let f := leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))
  let e := realificationDerivationLieEquiv (E := E) (G := G)
  have he (x : RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
      f (e x) = realificationLieEquiv (E := E) (G := G) x := by
    dsimp only [e, realificationDerivationLieEquiv]
    rw [LieEquiv.trans_apply]
    exact f.apply_symm_apply _
  obtain ⟨x, rfl⟩ := e.surjective D
  -- Normalize the equivalence coercion introduced by its surjectivity API.
  change f (realificationDerivationComplexStructure
      (realificationDerivationLieEquiv (E := E) (G := G) x)) =
    realificationComplexStructure (f (e x))
  rw [realificationDerivationComplexStructure_realificationDerivationLieEquiv, he, he,
    realificationComplexStructure_realificationLieEquiv]

/-- The induced complex structure is multiplication by `Complex.I` in complex tangent
coordinates. -/
-- Keep the complex structure opaque to simp so its algebraic bracket laws are normal forms.
theorem realificationDerivationComplexStructure_apply (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    realificationDerivationComplexStructure D =
      realificationDerivationLieEquiv (E := E) (G := G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm
          (Complex.I • RestrictScalars.addEquiv ℝ ℂ _
            ((realificationDerivationLieEquiv (E := E) (G := G)).symm D))) := by
  exact (realificationDerivationLieEquiv (E := E) (G := G)).complexStructure_apply D

/-- The induced endomorphism of real left-invariant derivations squares to minus the identity. -/
@[simp]
theorem realificationDerivationComplexStructure_sq :
    (realificationDerivationComplexStructure (E := E) (G := G)) ^ 2 = -1 := by
  exact (realificationDerivationLieEquiv (E := E) (G := G)).complexStructure_sq

/-- Two applications of the induced complex structure negate a real invariant derivation. -/
@[simp]
theorem realificationDerivationComplexStructure_apply_apply
    (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    realificationDerivationComplexStructure (realificationDerivationComplexStructure D) = -D := by
  exact (realificationDerivationLieEquiv (E := E) (G := G)).complexStructure_apply_apply D

/-- The complex structure commutes with the real derivation bracket in its first argument. -/
@[simp]
theorem realificationDerivationComplexStructure_lie_left (X Y : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    ⁅realificationDerivationComplexStructure (E := E) (G := G) X, Y⁆ =
      realificationDerivationComplexStructure (E := E) (G := G) ⁅X, Y⁆ := by
  exact (realificationDerivationLieEquiv (E := E) (G := G)).complexStructure_lie_left X Y

/-- The complex structure commutes with the real derivation bracket in its second argument. -/
@[simp]
theorem realificationDerivationComplexStructure_lie_right
    (X Y : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    ⁅X, realificationDerivationComplexStructure (E := E) (G := G) Y⁆ =
      realificationDerivationComplexStructure (E := E) (G := G) ⁅X, Y⁆ := by
  exact (realificationDerivationLieEquiv (E := E) (G := G)).complexStructure_lie_right X Y

end Derivation

end

end TauCeti.Lie
