/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.Lie.BaseChange.ComplexStructure
public import TauCeti.Geometry.Lie.RestrictScalars
public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Lie.Tangent.Differential
public import TauCeti.Geometry.Lie.Tangent.LieEquiv
public import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorField.RestrictScalars
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

The canonical `TauCeti.AlmostComplexStructure.ofRestrictScalars` transports multiplication by
`Complex.I` through the normalized underlying real-linear equivalences using the existing
`AlmostComplexStructure.transport`. Its square and bracket laws apply directly.

## Main results

* `TauCeti.Lie.realificationLieEquiv_apply` and
  `TauCeti.Lie.realificationLieEquiv_symm_apply`: agreement with the public fibre equivalence.
* `TauCeti.Lie.realificationLieEquiv_groupLieAlgebraMap` and
  `TauCeti.Lie.realificationLieEquiv_tangentAd`: compatibility with holomorphic differentials
  and tangent adjoint actions.
* `TauCeti.Lie.realificationDerivationLieEquiv_apply` and its inverse formula:
  the derivation comparison and evaluation at the identity.
* `TauCeti.Lie.realificationDerivationLieEquiv_complexStructure_evaluation`:
  evaluation intertwines the transported tangent and derivation complex structures.
* `TauCeti.Lie.realificationLieEquiv_complexStructure_groupLieAlgebraMap` and
  `TauCeti.Lie.realificationLieEquiv_complexStructure_tangentAd`: holomorphic differentials
  and tangent adjoint actions commute with the transported complex structures.
* `TauCeti.Lie.realificationDerivationLieEquiv_complexStructure_lieMap` and
  `TauCeti.Lie.realificationDerivationLieEquiv_complexStructure_Ad`: the corresponding
  naturality results on invariant derivations.

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

section Tangent

variable [Group G] [LieGroup 𝓘(ℂ, E) 3 G]

/-- The underlying real Lie-group structure used locally in the tangent comparison. -/
local instance realificationLieGroup : LieGroup 𝓘(ℝ, E) 3 G :=
  LieGroup.restrictScalars_self ℝ (𝕜 := ℂ)

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

private theorem realificationTangent_mulInvariantVectorField
    (v : GroupLieAlgebra 𝓘(ℂ, E) G) (g : G) :
    TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) g
        ((RestrictScalars.addEquiv ℝ ℂ _).symm (mulInvariantVectorField v g)) =
      mulInvariantVectorField (I := 𝓘(ℝ, E))
        (TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)
          ((RestrictScalars.addEquiv ℝ ℂ _).symm v)) g := by
  have h := MDifferentiableAt.mfderiv_restrictScalarsSelf_apply ℝ
    ((contMDiff_mul_left (I := 𝓘(ℂ, E)) (n := 3) (a := g)).mdifferentiableAt
      (by simp) (x := (1 : G))) ((RestrictScalars.addEquiv ℝ ℂ _).symm v)
  rw [mul_one] at h
  simp only [AddEquiv.apply_symm_apply] at h
  simp only [mulInvariantVectorField]
  exact h

variable [CompleteSpace E]

private theorem realificationTangent_lie (v w : GroupLieAlgebra 𝓘(ℂ, E) G) :
    TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)
        ((RestrictScalars.addEquiv ℝ ℂ _).symm ⁅v, w⁆) =
      ⁅(TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)
          ((RestrictScalars.addEquiv ℝ ℂ _).symm v) : GroupLieAlgebra 𝓘(ℝ, E) G),
        TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)
          ((RestrictScalars.addEquiv ℝ ℂ _).symm w)⁆ := by
  rw [GroupLieAlgebra.bracket_def, GroupLieAlgebra.bracket_def]
  simpa only [realificationTangent_mulInvariantVectorField] using
    (VectorField.mlieBracket_restrictScalars ℝ
      (V := mulInvariantVectorField v) (W := mulInvariantVectorField w) (x := (1 : G))
      ((contMDiff_mulInvariantVectorField v).mdifferentiable (by simp)).mdifferentiableAt
      ((contMDiff_mulInvariantVectorField w).mdifferentiable (by simp)).mdifferentiableAt)

/-- The native tangent Lie algebra of a complex Lie group, with scalars restricted to `ℝ`,
is the Lie algebra of the underlying real Lie group. -/
def realificationLieEquiv :
    RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G) ≃ₗ⁅ℝ⁆ GroupLieAlgebra 𝓘(ℝ, E) G :=
  { toFun := TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)
    invFun := (TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)).symm
    left_inv := (TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)).left_inv
    right_inv := (TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)).right_inv
    map_add' := (TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)).map_add
    map_smul' := (TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)).map_smul
    map_lie' := by
      intro x y
      have h := realificationTangent_lie (E := E) (G := G)
        (RestrictScalars.addEquiv ℝ ℂ _ x) (RestrictScalars.addEquiv ℝ ℂ _ y)
      rw [← RestrictScalars.addEquiv_lie, AddEquiv.symm_apply_apply] at h
      simpa only [AddEquiv.symm_apply_apply] using h }

/-- The real Lie equivalence is the public fibre equivalence at the identity. -/
@[simp]
theorem realificationLieEquiv_apply
    (x : RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
    realificationLieEquiv (E := E) (G := G) x =
      (tangentSpaceCastModel 𝓘(ℝ, E) (1 : G)).symm
        (tangentSpaceCastModel 𝓘(ℂ, E) (1 : G) (RestrictScalars.addEquiv ℝ ℂ _ x)) := by
  exact TangentSpace.restrictScalarsSelfLinearEquiv_apply ℝ (1 : G) x

/-- Inverse Lie-algebra realification is the inverse public fibre equivalence. -/
@[simp]
theorem realificationLieEquiv_symm_apply (x : GroupLieAlgebra 𝓘(ℝ, E) G) :
    (realificationLieEquiv (E := E) (G := G)).symm x =
      (RestrictScalars.addEquiv ℝ ℂ _).symm
        ((tangentSpaceCastModel 𝓘(ℂ, E) (1 : G)).symm
          (tangentSpaceCastModel 𝓘(ℝ, E) (1 : G) x)) := by
  rw [LieEquiv.symm_apply_eq, realificationLieEquiv_apply]
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
  have h := MDifferentiableAt.mfderiv_restrictScalarsSelf_apply ℝ hφ
    ((RestrictScalars.addEquiv ℝ ℂ _).symm x)
  rw [conjDiffeomorph_apply, mul_one, mul_inv_cancel] at h
  simp only [AddEquiv.apply_symm_apply] at h
  have heq : (TauCeti.Lie.conjDiffeomorph (I := 𝓘(ℝ, E)) (n := 1) g : G → G) =
      (TauCeti.Lie.conjDiffeomorph (I := 𝓘(ℂ, E)) (n := 1) g : G → G) := by
    funext y
    simp only [TauCeti.Lie.conjDiffeomorph_apply]
  have hR := DFunLike.congr_fun
    (mfderiv_congr (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (x := (1 : G)) heq)
    (TangentSpace.restrictScalarsSelfLinearEquiv ℝ (A := ℂ) (1 : G)
      ((RestrictScalars.addEquiv ℝ ℂ _).symm x))
  simp only [TauCeti.Lie.tangentAd_apply, TauCeti.Lie.adjointContinuousLinearMap_apply]
  rw [realificationLieEquiv_apply, realificationLieEquiv_apply]
  rw [TangentSpace.restrictScalarsSelfLinearEquiv_apply] at hR
  rw [TangentSpace.restrictScalarsSelfLinearEquiv_apply,
    TangentSpace.restrictScalarsSelfLinearEquiv_apply] at h
  exact h.trans hR.symm

/-- The adjoint action commutes with the transported complex structure. -/
theorem realificationLieEquiv_complexStructure_tangentAd
    (g : G) (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    tangentAd (I := 𝓘(ℝ, E)) g
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv X) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
        (realificationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv
        (tangentAd (I := 𝓘(ℝ, E)) g X) := by
  apply (realificationLieEquiv (E := E) (G := G)).transport_ofRestrictScalars_naturality
    (realificationLieEquiv (E := E) (G := G))
    (tangentAd (I := 𝓘(ℂ, E)) g).toLinearEquiv.toLinearMap
    (tangentAd (I := 𝓘(ℝ, E)) g).toLinearEquiv.toLinearMap
  intro y
  have h := (realificationLieEquiv_tangentAd g (RestrictScalars.addEquiv ℝ ℂ _ y)).symm
  rw [AddEquiv.symm_apply_apply] at h
  simpa only [LieEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe] using h

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
  have h := MDifferentiableAt.mfderiv_restrictScalarsSelf_apply ℝ hφ
    ((RestrictScalars.addEquiv ℝ ℂ _).symm x)
  rw [φ.map_one] at h
  simp only [AddEquiv.apply_symm_apply] at h
  rw [MonoidHom.groupLieAlgebraMap_apply, MonoidHom.groupLieAlgebraMap_apply,
    realificationLieEquiv_apply, realificationLieEquiv_apply]
  rw [TangentSpace.restrictScalarsSelfLinearEquiv_apply,
    TangentSpace.restrictScalarsSelfLinearEquiv_apply] at h
  exact h

/-- The differential of a holomorphic homomorphism commutes with the transported complex
structures on its source and target. -/
theorem realificationLieEquiv_complexStructure_groupLieAlgebraMap (φ : G →* K)
    (hφ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) φ 1) (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    φ.groupLieAlgebraMap 𝓘(ℝ, E) 𝓘(ℝ, F)
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv X) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, F) K)).transport
        (realificationLieEquiv (E := F) (G := K)).restrictScalarsLinearEquiv
        (φ.groupLieAlgebraMap 𝓘(ℝ, E) 𝓘(ℝ, F) X) := by
  apply (realificationLieEquiv (E := E) (G := G)).transport_ofRestrictScalars_naturality
    (realificationLieEquiv (E := F) (G := K))
    (φ.groupLieAlgebraMap 𝓘(ℂ, E) 𝓘(ℂ, F))
    (φ.groupLieAlgebraMap 𝓘(ℝ, E) 𝓘(ℝ, F))
  intro y
  have h := (realificationLieEquiv_groupLieAlgebraMap φ hφ
    (RestrictScalars.addEquiv ℝ ℂ _ y)).symm
  rw [AddEquiv.symm_apply_apply] at h
  simpa only [LieEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe] using h

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

/-- Evaluation at the identity intertwines the transported complex structures on invariant
derivations and tangent vectors. -/
theorem realificationDerivationLieEquiv_complexStructure_evaluation
    (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
        (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationDerivationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv D) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
        (realificationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
          (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D) := by
  let f := leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))
  have he : (realificationDerivationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv.trans
      f.toLinearEquiv = (realificationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv := by
    ext x
    simp only [LinearEquiv.trans_apply, LieEquiv.restrictScalarsLinearEquiv_apply,
      LieEquiv.coe_toLinearEquiv, realificationDerivationLieEquiv, LieEquiv.trans_apply]
    exact f.apply_symm_apply _
  have h := (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G))
    |>.transport_trans
      (realificationDerivationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv f.toLinearEquiv
  rw [he] at h
  have hD := congrArg (fun J : AlmostComplexStructure (GroupLieAlgebra 𝓘(ℝ, E) G) =>
    J.toLinearMap (f D)) h
  rw [AlmostComplexStructure.transport_apply] at hD
  have hf : f.toLinearEquiv.symm (f D) = D := by
    simpa only [LieEquiv.coe_toLinearEquiv] using f.toLinearEquiv.symm_apply_apply D
  rw [hf] at hD
  exact hD

/-- The real adjoint action on invariant derivations commutes with their complex structure. -/
theorem realificationDerivationLieEquiv_complexStructure_Ad
    (g : G) (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    Ad (I := 𝓘(ℝ, E)) g
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationDerivationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv D) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
        (realificationDerivationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv
        (Ad (I := 𝓘(ℝ, E)) g D) := by
  apply (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))).toLinearEquiv
      |>.injective
  simpa only [LieEquiv.coe_toLinearEquiv,
    leftInvariantDerivationLieEquivGroupLieAlgebra_Ad,
    realificationDerivationLieEquiv_complexStructure_evaluation] using
    (realificationLieEquiv_complexStructure_tangentAd g
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
        (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℝ F]
  {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace F K] [LieGroup 𝓘(ℂ, F) ∞ K]

/-- The derivation Lie map of a real smooth homomorphism whose differential is complex-linear
commutes with the transported complex structures. -/
theorem realificationDerivationLieEquiv_complexStructure_lieMap
    (φ : ContMDiffMonoidMorphism 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ G K)
    (hφ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) φ 1)
    (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    lieMap φ
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationDerivationLieEquiv (E := E) (G := G)).restrictScalarsLinearEquiv D) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, F) K)).transport
        (realificationDerivationLieEquiv (E := F) (G := K)).restrictScalarsLinearEquiv
        (lieMap φ D) := by
  apply (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, F)) (G := K)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, F)) (n := ∞) (by simp) (1 : K))).toLinearEquiv
      |>.injective
  simp only [LieEquiv.coe_toLinearEquiv,
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap,
    realificationDerivationLieEquiv_complexStructure_evaluation]
  have h := realificationLieEquiv_complexStructure_groupLieAlgebraMap (MonoidHom.ofClass φ) hφ
    (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D)
  simpa only [MonoidHom.groupLieAlgebraMap_apply, MonoidHom.coe_ofClass] using h

end Derivation

end

end TauCeti.Lie
