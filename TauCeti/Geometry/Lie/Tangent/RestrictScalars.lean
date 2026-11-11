/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Lie
public import TauCeti.Geometry.Lie.RestrictScalars
public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.Geometry.Lie.Functor
public import TauCeti.Geometry.Lie.Tangent.Differential
public import TauCeti.Geometry.Lie.Tangent.LieEquiv
public import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorField.RestrictScalars
import TauCeti.Geometry.Symplectic.Complex.Module.Hom

/-!
# Scalar restriction of tangent Lie algebras

For compatible normed fields `R → A` and a shared atlas, scalar restriction identifies the
native tangent Lie algebra over `A` with the tangent Lie algebra over `R`. The comparison is
its public fibre equivalence at the identity. It preserves brackets, differentials of maps
differentiable over `A` and tangent adjoint actions. The two Lie-group structures have the
standard `minSmoothness` regularity for their respective fields, with a complete model.
No finite-dimensionality hypothesis is needed for this tangent comparison.

For a complex Lie group, use `LieGroup.restrictScalars_self ℝ` locally for the underlying real
structure. For finite-dimensional smooth complex Lie groups the comparison also identifies
real left-invariant derivations. The canonical bundled almost complex structure, transported
through either comparison, squares to minus the identity and commutes with brackets,
holomorphic differentials and adjoint actions.

## Main definitions

* `TauCeti.Lie.restrictScalarsLieEquiv`: the tangent Lie equivalence over compatible normed fields.
* `TauCeti.Lie.realificationDerivationLieEquiv`: the corresponding equivalence with real
  left-invariant derivations for finite-dimensional smooth complex Lie groups.

The canonical `TauCeti.AlmostComplexStructure.ofRestrictScalars` transports multiplication by
`Complex.I` through the normalized underlying real-linear equivalences using the existing
`AlmostComplexStructure.transport`. Its square and bracket laws apply directly.

## Main results

* `TauCeti.Lie.restrictScalarsLieEquiv_apply` and
  `TauCeti.Lie.restrictScalarsLieEquiv_symm_apply`: agreement with the public fibre equivalence.
* `TauCeti.Lie.restrictScalarsLieEquiv_groupLieAlgebraMap` and
  `TauCeti.Lie.restrictScalarsLieEquiv_tangentAd`: compatibility with holomorphic differentials
  and tangent adjoint actions.
* `TauCeti.Lie.realificationDerivationLieEquiv_apply` and its inverse formula:
  the derivation comparison and evaluation at the identity.
* `TauCeti.Lie.leftInvariantDerivationLieEquivGroupLieAlgebra_transport_ofRestrictScalars`:
  evaluation intertwines the transported tangent and derivation complex structures.
* `MonoidHom.groupLieAlgebraMap_transport_ofRestrictScalars` and
  `TauCeti.Lie.tangentAd_transport_ofRestrictScalars`: holomorphic differentials
  and tangent adjoint actions commute with the transported complex structures.
* `TauCeti.Lie.lieMap_transport_ofRestrictScalars` and
  `TauCeti.Lie.Ad_transport_ofRestrictScalars`: the corresponding
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

private local instance restrictScalarsLieGroupOne
    {𝕜 E G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(𝕜, E) (minSmoothness 𝕜 3) G] : LieGroup 𝓘(𝕜, E) 1 G :=
  LieGroup.of_le (n := minSmoothness 𝕜 3)
    ((by norm_num : (1 : ℕ∞ω) ≤ 3).trans le_minSmoothness)

private local instance restrictScalarsLieManifoldTwo
    {𝕜 E G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(𝕜, E) (minSmoothness 𝕜 3) G] :
    IsManifold 𝓘(𝕜, E) (minSmoothness 𝕜 2) G :=
  IsManifold.of_le (n := minSmoothness 𝕜 3) (minSmoothness_monotone (𝕜 := 𝕜) (by norm_num))

section TangentRestriction

variable (R : Type*) {A : Type*} [NontriviallyNormedField R] [NontriviallyNormedField A]
  [NormedAlgebra R A] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace A E] [NormedSpace R E] [IsScalarTower R A E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup 𝓘(A, E) (minSmoothness A 3) G]
  [LieGroup 𝓘(R, E) (minSmoothness R 3) G]

omit [LieGroup 𝓘(R, E) (minSmoothness R 3) G] in
private theorem restrictScalarsTangent_mulInvariantVectorField
    (v : GroupLieAlgebra 𝓘(A, E) G) (g : G) :
    TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) g
        ((RestrictScalars.addEquiv R A _).symm (mulInvariantVectorField v g)) =
      mulInvariantVectorField (I := 𝓘(R, E))
        (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)
          ((RestrictScalars.addEquiv R A _).symm v)) g := by
  have h := MDifferentiableAt.mfderiv_restrictScalarsSelf_apply R
    ((contMDiff_mul_left (I := 𝓘(A, E)) (n := minSmoothness A 3) (a := g)).mdifferentiableAt
      (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 3) le_minSmoothness))
      (x := (1 : G))) ((RestrictScalars.addEquiv R A _).symm v)
  rw [mul_one] at h
  simp only [AddEquiv.apply_symm_apply] at h
  simp only [mulInvariantVectorField]
  exact h

variable [CompleteSpace E]

private theorem restrictScalarsTangent_lie (v w : GroupLieAlgebra 𝓘(A, E) G) :
    TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)
        ((RestrictScalars.addEquiv R A _).symm ⁅v, w⁆) =
      ⁅(TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)
          ((RestrictScalars.addEquiv R A _).symm v) : GroupLieAlgebra 𝓘(R, E) G),
        TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)
          ((RestrictScalars.addEquiv R A _).symm w)⁆ := by
  have hA : minSmoothness A 2 ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) le_minSmoothness).ne'
  rw [GroupLieAlgebra.bracket_def, GroupLieAlgebra.bracket_def]
  simpa only [restrictScalarsTangent_mulInvariantVectorField] using
    (VectorField.mlieBracket_restrictScalars R
      (V := mulInvariantVectorField v) (W := mulInvariantVectorField w) (x := (1 : G))
      ((contMDiff_mulInvariantVectorField v).mdifferentiable hA).mdifferentiableAt
      ((contMDiff_mulInvariantVectorField w).mdifferentiable hA).mdifferentiableAt)

/-- Scalar restriction identifies the native tangent Lie algebras over compatible fields. -/
def restrictScalarsLieEquiv :
    RestrictScalars R A (GroupLieAlgebra 𝓘(A, E) G) ≃ₗ⁅R⁆ GroupLieAlgebra 𝓘(R, E) G :=
  { toFun := TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)
    invFun := (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)).symm
    left_inv := (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)).left_inv
    right_inv := (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)).right_inv
    map_add' := (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)).map_add
    map_smul' := (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)).map_smul
    map_lie' := by
      intro x y
      have h := restrictScalarsTangent_lie R (E := E) (G := G)
        (RestrictScalars.addEquiv R A _ x) (RestrictScalars.addEquiv R A _ y)
      rw [← RestrictScalars.addEquiv_lie, AddEquiv.symm_apply_apply] at h
      simpa only [AddEquiv.symm_apply_apply] using h }

/-- The tangent Lie equivalence is the public fibre equivalence at the identity. -/
@[simp]
theorem restrictScalarsLieEquiv_apply
    (x : RestrictScalars R A (GroupLieAlgebra 𝓘(A, E) G)) :
    restrictScalarsLieEquiv R (E := E) (G := G) x =
      TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G) x := by
  rfl

/-- The inverse tangent comparison is the inverse public fibre equivalence. -/
@[simp]
theorem restrictScalarsLieEquiv_symm_apply (x : GroupLieAlgebra 𝓘(R, E) G) :
    (restrictScalarsLieEquiv R (E := E) (G := G)).symm x =
      (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)).symm x := by
  rfl

/-- The scalar-restriction equivalence intertwines tangent adjoint actions. -/
theorem restrictScalarsLieEquiv_tangentAd (g : G) (x : GroupLieAlgebra 𝓘(A, E) G) :
    restrictScalarsLieEquiv R (E := E) (G := G)
        ((RestrictScalars.addEquiv R A _).symm (tangentAd (I := 𝓘(A, E)) g x)) =
      TauCeti.Lie.tangentAd (I := 𝓘(R, E)) g (restrictScalarsLieEquiv R (E := E) (G := G)
        ((RestrictScalars.addEquiv R A _).symm x)) := by
  have hφ := (TauCeti.Lie.conjDiffeomorph (I := 𝓘(A, E)) (n := 1) g).mdifferentiable
    one_ne_zero (1 : G)
  have h := MDifferentiableAt.mfderiv_restrictScalarsSelf_apply R hφ
    ((RestrictScalars.addEquiv R A _).symm x)
  rw [conjDiffeomorph_apply, mul_one, mul_inv_cancel] at h
  simp only [AddEquiv.apply_symm_apply] at h
  have heq : (TauCeti.Lie.conjDiffeomorph (I := 𝓘(R, E)) (n := 1) g : G → G) =
      (TauCeti.Lie.conjDiffeomorph (I := 𝓘(A, E)) (n := 1) g : G → G) := by
    funext y
    simp only [TauCeti.Lie.conjDiffeomorph_apply]
  have hR := DFunLike.congr_fun
    (mfderiv_congr (I := 𝓘(R, E)) (I' := 𝓘(R, E)) (x := (1 : G)) heq)
    (TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) (1 : G)
      ((RestrictScalars.addEquiv R A _).symm x))
  simp only [TauCeti.Lie.tangentAd_apply, TauCeti.Lie.adjointContinuousLinearMap_apply]
  rw [restrictScalarsLieEquiv_apply, restrictScalarsLieEquiv_apply]
  exact h.trans hR.symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace A F] [NormedSpace R F]
  [IsScalarTower R A F] [CompleteSpace F]
  {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace F K]
  [LieGroup 𝓘(A, F) (minSmoothness A 3) K]
  [LieGroup 𝓘(R, F) (minSmoothness R 3) K]

/-- Scalar restriction commutes with the differential of a homomorphism differentiable over `A`
at the identity. The source and target groups and models may have different universes. -/
theorem restrictScalarsLieEquiv_groupLieAlgebraMap (φ : G →* K)
    (hφ : MDifferentiableAt 𝓘(A, E) 𝓘(A, F) φ 1)
    (x : GroupLieAlgebra 𝓘(A, E) G) :
    restrictScalarsLieEquiv R (E := F) (G := K)
        ((RestrictScalars.addEquiv R A _).symm
          (φ.groupLieAlgebraMap 𝓘(A, E) 𝓘(A, F) x)) =
      φ.groupLieAlgebraMap 𝓘(R, E) 𝓘(R, F) (restrictScalarsLieEquiv R (E := E) (G := G)
          ((RestrictScalars.addEquiv R A _).symm x)) := by
  have h := MDifferentiableAt.mfderiv_restrictScalarsSelf_apply R hφ
    ((RestrictScalars.addEquiv R A _).symm x)
  rw [φ.map_one] at h
  simp only [AddEquiv.apply_symm_apply] at h
  rw [MonoidHom.groupLieAlgebraMap_apply, MonoidHom.groupLieAlgebraMap_apply,
    restrictScalarsLieEquiv_apply, restrictScalarsLieEquiv_apply]
  exact h

end TangentRestriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G]

section Tangent

variable [Group G] [LieGroup 𝓘(ℂ, E) 3 G] [LieGroup 𝓘(ℝ, E) 3 G] [CompleteSpace E]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The adjoint action commutes with the transported complex structure. -/
theorem tangentAd_transport_ofRestrictScalars
    (g : G) (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    tangentAd (I := 𝓘(ℝ, E)) g
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv X) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
        (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv
        (tangentAd (I := 𝓘(ℝ, E)) g X) := by
  apply AlmostComplexStructure.ofRestrictScalars_transport_naturality
    (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv
    (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv
    (tangentAd (I := 𝓘(ℂ, E)) g).toLinearEquiv.toLinearMap
    (tangentAd (I := 𝓘(ℝ, E)) g).toLinearEquiv.toLinearMap
  intro x
  simpa only [LieEquiv.toRealLinearEquiv_apply, LieEquiv.coe_toLinearEquiv,
    LinearEquiv.coe_coe] using (restrictScalarsLieEquiv_tangentAd ℝ g x).symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace F K]
  [LieGroup 𝓘(ℂ, F) 3 K] [LieGroup 𝓘(ℝ, F) 3 K]

/-- The differential of a holomorphic homomorphism commutes with the transported complex
structures on its source and target. -/
theorem _root_.MonoidHom.groupLieAlgebraMap_transport_ofRestrictScalars (φ : G →* K)
    (hφ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) φ 1) (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    φ.groupLieAlgebraMap 𝓘(ℝ, E) 𝓘(ℝ, F)
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv X) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, F) K)).transport
        (restrictScalarsLieEquiv ℝ (A := ℂ) (E := F) (G := K)).toRealLinearEquiv
        (φ.groupLieAlgebraMap 𝓘(ℝ, E) 𝓘(ℝ, F) X) := by
  apply AlmostComplexStructure.ofRestrictScalars_transport_naturality
    (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv
    (restrictScalarsLieEquiv ℝ (A := ℂ) (E := F) (G := K)).toRealLinearEquiv
    (φ.groupLieAlgebraMap 𝓘(ℂ, E) 𝓘(ℂ, F))
    (φ.groupLieAlgebraMap 𝓘(ℝ, E) 𝓘(ℝ, F))
  intro x
  simpa only [LieEquiv.toRealLinearEquiv_apply, ContinuousLinearMap.coe_coe] using
    (restrictScalarsLieEquiv_groupLieAlgebraMap ℝ φ hφ x).symm

end Tangent

section Derivation

variable [FiniteDimensional ℝ E] [Group G]
  [LieGroup 𝓘(ℂ, E) ∞ G] [LieGroup 𝓘(ℝ, E) ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The complex tangent Lie algebra with scalars restricted to `ℝ` is the real
left-invariant derivation algebra of a finite-dimensional smooth complex Lie group. -/
def realificationDerivationLieEquiv :
    RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G) ≃ₗ⁅ℝ⁆
      LeftInvariantDerivation 𝓘(ℝ, E) G :=
  (TauCeti.Lie.restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).trans
    (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))).symm

/-- Realification sends a complex tangent vector to its real invariant derivation. -/
@[simp]
theorem realificationDerivationLieEquiv_apply
    (x : RestrictScalars ℝ ℂ (GroupLieAlgebra 𝓘(ℂ, E) G)) :
    realificationDerivationLieEquiv (E := E) (G := G) x =
      tangentToLeftInvariantDerivation
        (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G) x) := by
  rw [realificationDerivationLieEquiv, LieEquiv.trans_apply,
    leftInvariantDerivationLieEquivGroupLieAlgebra_symm_apply]

/-- The inverse real derivation comparison is evaluation at the identity followed by inverse
realification of the tangent vector. -/
@[simp]
theorem realificationDerivationLieEquiv_symm_apply (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    (realificationDerivationLieEquiv (E := E) (G := G)).symm D =
      (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).symm
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
          (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D) := by
  rfl

/-- Evaluation at the identity intertwines the transported complex structures on invariant
derivations and tangent vectors. -/
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_transport_ofRestrictScalars
    (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
        (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationDerivationLieEquiv (E := E) (G := G)).toRealLinearEquiv D) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
        (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv
        (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
          (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D) := by
  let f := leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))
  have he : (realificationDerivationLieEquiv (E := E) (G := G)).toRealLinearEquiv.trans
      f.toLinearEquiv =
        (restrictScalarsLieEquiv ℝ (A := ℂ) (E := E) (G := G)).toRealLinearEquiv := by
    ext x
    simp only [LinearEquiv.trans_apply, LieEquiv.toRealLinearEquiv_apply,
      LieEquiv.coe_toLinearEquiv, realificationDerivationLieEquiv, LieEquiv.trans_apply]
    exact f.apply_symm_apply _
  have h := (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G))
    |>.transport_trans
      (realificationDerivationLieEquiv (E := E) (G := G)).toRealLinearEquiv f.toLinearEquiv
  rw [he] at h
  have hD := congrArg (fun J : AlmostComplexStructure (GroupLieAlgebra 𝓘(ℝ, E) G) =>
    J.toLinearMap (f D)) h
  rw [AlmostComplexStructure.transport_apply] at hD
  have hf : f.toLinearEquiv.symm (f D) = D := by
    simpa only [LieEquiv.coe_toLinearEquiv] using f.toLinearEquiv.symm_apply_apply D
  rw [hf] at hD
  exact hD

/-- The real adjoint action on invariant derivations commutes with their complex structure. -/
theorem Ad_transport_ofRestrictScalars
    (g : G) (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    Ad (I := 𝓘(ℝ, E)) g
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationDerivationLieEquiv (E := E) (G := G)).toRealLinearEquiv D) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
        (realificationDerivationLieEquiv (E := E) (G := G)).toRealLinearEquiv
        (Ad (I := 𝓘(ℝ, E)) g D) := by
  apply (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G))).toLinearEquiv
      |>.injective
  simpa only [LieEquiv.coe_toLinearEquiv,
    leftInvariantDerivationLieEquivGroupLieAlgebra_Ad,
    leftInvariantDerivationLieEquivGroupLieAlgebra_transport_ofRestrictScalars] using
    (tangentAd_transport_ofRestrictScalars g
      (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
        (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℝ F]
  {K : Type*} [Group K] [TopologicalSpace K] [ChartedSpace F K]
  [LieGroup 𝓘(ℂ, F) ∞ K] [LieGroup 𝓘(ℝ, F) ∞ K]

/-- The derivation Lie map of a real smooth homomorphism whose differential is complex-linear
commutes with the transported complex structures. -/
theorem lieMap_transport_ofRestrictScalars
    (φ : ContMDiffMonoidMorphism 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ G K)
    (hφ : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) φ 1)
    (D : LeftInvariantDerivation 𝓘(ℝ, E) G) :
    lieMap φ
        ((AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, E) G)).transport
          (realificationDerivationLieEquiv (E := E) (G := G)).toRealLinearEquiv D) =
      (AlmostComplexStructure.ofRestrictScalars (GroupLieAlgebra 𝓘(ℂ, F) K)).transport
        (realificationDerivationLieEquiv (E := F) (G := K)).toRealLinearEquiv
        (lieMap φ D) := by
  apply (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, F)) (G := K)
    (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, F)) (n := ∞) (by simp) (1 : K))).toLinearEquiv
      |>.injective
  simp only [LieEquiv.coe_toLinearEquiv,
    leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap,
    leftInvariantDerivationLieEquivGroupLieAlgebra_transport_ofRestrictScalars]
  have h := (MonoidHom.ofClass φ).groupLieAlgebraMap_transport_ofRestrictScalars hφ
    (leftInvariantDerivationLieEquivGroupLieAlgebra (I := 𝓘(ℝ, E)) (G := G)
      (ContMDiffMul.isInteriorPoint (I := 𝓘(ℝ, E)) (n := ∞) (by simp) (1 : G)) D)
  simpa only [MonoidHom.groupLieAlgebraMap_apply, MonoidHom.coe_ofClass] using h

end Derivation

end

end TauCeti.Lie
