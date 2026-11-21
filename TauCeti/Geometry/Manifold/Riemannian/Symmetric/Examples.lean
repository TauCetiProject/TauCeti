/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import TauCeti.Geometry.Manifold.Riemannian.Circle
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.WithMetric
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.UpperHalfSpace
public import TauCeti.Geometry.Manifold.Riemannian.Symmetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.WarpedProd
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Scalar

/-!
# Examples and non-examples of Riemannian symmetric spaces

This file constructs the basic positive examples of Riemannian symmetric spaces and the two
canonical negative controls separating local symmetry, geodesic completeness, and global symmetry:

* **Real inner product spaces**: every real inner product space `F` (in particular `EuclideanSpace
  ℝ (Fin n)`) is a Riemannian symmetric space, with geodesic symmetry at `p` given by the affine
  point reflection `x ↦ 2 p - x`.
* **Round unit spheres**: every round unit sphere `Metric.sphere (0 : E) 1` of dimension `n` is a
  Riemannian symmetric space, with geodesic symmetry at `p` given by ambient orthogonal reflection
  in the line `ℝ ∙ p`.
* **Real hyperbolic spaces**: every upper half-space model `UpperHalfSpace E` is a Riemannian
  symmetric space; the isometry group acts transitively, and at `(0, 1)` the composite of unit
  inversion about `(0, 0)` with horizontal negation `(x, t) ↦ (-x, t)` is a geodesic symmetry.
* **The unit circle and flat 2-torus**: `Circle` with its round metric and the flat product torus
  `Circle × Circle` are Riemannian symmetric spaces.
* **Proper open subsets of Euclidean space** (in particular punctured Euclidean space `F \ {0}`):
  every open subset of a finite-dimensional real inner product space is flat, hence has parallel
  curvature (`∇R = 0`), but no nonempty proper open subset is a Riemannian symmetric space because
  it is not geodesically complete.
* **Complete simply connected surfaces of nonconstant curvature**: on `ℝ × ℝ`, any warped
  metric `dx² + f(x)² dy²` with `f` smooth and bounded away from zero is geodesically complete
  and simply connected, with scalar curvature `-2 f''(x) / f(x)`. Whenever `f'' / f` is
  nonconstant (for example `f(x) = x² + 1`), the surface fails to have parallel curvature and is
  therefore not a Riemannian symmetric space.

## Main results

* `TauCeti.isGeodesicSymmetryAt_pointReflection` and
  `TauCeti.instIsRiemannianSymmetricSpaceInnerProductSpace`: every real inner product space is a
  Riemannian symmetric space.
* `TauCeti.isGeodesicSymmetryAt_unitSphereReflection` and
  `TauCeti.instIsRiemannianSymmetricSpaceSphere`: every round unit sphere is a Riemannian
  symmetric space.
* `TauCeti.instIsRiemannianSymmetricSpaceUpperHalfSpace`: every upper half-space model of real
  hyperbolic space is a Riemannian symmetric space.
* `TauCeti.isRiemannianSymmetricSpace_circle` and
  `TauCeti.isRiemannianSymmetricSpace_circle_prod`: the round unit circle and the flat 2-torus are
  Riemannian symmetric spaces.
* `TauCeti.hasParallelCurvature_opens_innerProductSpace`,
  `TauCeti.not_isRiemannianSymmetricSpace_opens_innerProductSpace`, and
  `TauCeti.not_isRiemannianSymmetricSpace_compl_singleton`: proper open subsets of Euclidean space
  (including punctured space `F \ {x₀}`) are locally symmetric but not globally symmetric.
* `TauCeti.warpedPlaneMetric`, `TauCeti.scalarCurvature_warpedPlaneMetric`,
  `TauCeti.isGeodesicallyCompleteAt_withMetric_warpedPlaneMetric`,
  `TauCeti.not_hasParallelCurvature_withMetric_warpedPlaneMetric`, and
  `TauCeti.not_isRiemannianSymmetricSpace_withMetric_warpedPlaneMetric`: complete simply connected
  warped planes with nonconstant `f'' / f` are not symmetric spaces, instantiated for
  `f(x) = x² + 1`.

## References

* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, AMS (2001),
  Ch. IV, §1–3.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Wiley (1969),
  Ch. XI, §1–3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 3, 6, 7.
-/

public section

open Bundle CovariantDerivative Manifold Metric Module Set TopologicalSpace
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold NNReal TauCeti

noncomputable section

namespace TauCeti

/-! ### Real inner product spaces -/

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- In any real inner product space, the affine point reflection `x ↦ 2 p - x` is a geodesic
symmetry at `p`. -/
theorem isGeodesicSymmetryAt_pointReflection (p : F) :
    IsGeodesicSymmetryAt (I := 𝓘(ℝ, F))
      (AffineIsometryEquiv.pointReflection ℝ p).toRiemannianIsometry p where
  apply_eq := by
    simp [AffineIsometryEquiv.pointReflection_self]
  mul_self := by
    ext x
    simp [AffineIsometryEquiv.pointReflection_involutive p x]
  mfderiv_eq := by
    have hfun : ⇑(AffineIsometryEquiv.pointReflection ℝ p).toRiemannianIsometry =
        fun x : F ↦ (p + p) - x := by
      funext x
      simp [AffineIsometryEquiv.pointReflection_apply]
      abel
    have hd : HasFDerivAt (fun x : F ↦ (p + p) - x) (-ContinuousLinearMap.id ℝ F) p := by
      have h := (hasFDerivAt_const (𝕜 := ℝ) (p + p) p).sub (hasFDerivAt_id (𝕜 := ℝ) p)
      rw [zero_sub] at h
      exact h
    rw [hfun]
    exact hd.hasMFDerivAt.mfderiv

/-- Every real inner product space (in particular Euclidean space `EuclideanSpace ℝ (Fin n)`) is a
Riemannian symmetric space. -/
instance instIsRiemannianSymmetricSpaceInnerProductSpace :
    IsRiemannianSymmetricSpace 𝓘(ℝ, F) F where
  exists_isGeodesicSymmetryAt p :=
    ⟨(AffineIsometryEquiv.pointReflection ℝ p).toRiemannianIsometry,
      isGeodesicSymmetryAt_pointReflection p⟩

end InnerProductSpace

/-! ### Round unit spheres -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]

/-- On the round unit sphere, ambient orthogonal reflection across the radial line `ℝ ∙ p` is a
geodesic symmetry at `p`. -/
theorem isGeodesicSymmetryAt_unitSphereReflection (p : sphere (0 : E) 1) :
    IsGeodesicSymmetryAt (I := 𝓡 n)
      (LinearIsometryEquiv.unitSphereRiemannianIsometry (n := n) (k := n)
        (ℝ ∙ (p : E)).reflection) p where
  apply_eq := by
    apply Subtype.ext
    rw [LinearIsometryEquiv.coe_unitSphereRiemannianIsometry_apply]
    exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self (p : E))
  mul_self := by
    ext x
    simp [RiemannianIsometry.mul_apply]
  mfderiv_eq := by
    let e : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (p : E)).reflection
    have hep : LinearIsometryEquiv.unitSphereRiemannianIsometry (n := n) (k := n) e p = p := by
      apply Subtype.ext
      rw [LinearIsometryEquiv.coe_unitSphereRiemannianIsometry_apply]
      exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self (p : E))
    ext v
    have hstep : ∀ {q : sphere (0 : E) 1} (_ : q = p) (w : TangentSpace (𝓡 n) q)
        (w' : TangentSpace (𝓡 n) p),
        (w : EuclideanSpace ℝ (Fin n)) = w' →
        mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) q w =
          mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p w' := by
      rintro q rfl w _ rfl
      rfl
    apply injective_mvfderiv_subtypeVal_sphere (n := n) p
    have hcoe := LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv (n := n) (k := n) e p v
    rw [← LinearIsometryEquiv.coe_unitSphereRiemannianIsometry (n := n) (k := n)] at hcoe
    have hmv : mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p
        (mfderiv (𝓡 n) (𝓡 n)
          (LinearIsometryEquiv.unitSphereRiemannianIsometry (n := n) (k := n) e) p v) =
        e (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) :=
      (hstep hep _ _ rfl).symm.trans hcoe
    rw [hmv]
    have horth :
        inner ℝ (p : E) (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) = 0 :=
      inner_coe_mvfderiv_subtypeVal_sphere p v
    have hrefl : e (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) =
        -(mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) := by
      dsimp only [e]
      rw [Submodule.reflection_singleton_apply, horth, RCLike.ofReal_real_eq_id, id_eq, zero_div,
        zero_smul, smul_zero, zero_sub]
    rw [hrefl]
    change -(mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) =
      mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p (-v)
    rw [map_neg]

/-- Every round unit sphere `Metric.sphere (0 : E) 1` is a Riemannian symmetric space. -/
instance instIsRiemannianSymmetricSpaceSphere :
    IsRiemannianSymmetricSpace (𝓡 n) (sphere (0 : E) 1) where
  exists_isGeodesicSymmetryAt p :=
    ⟨LinearIsometryEquiv.unitSphereRiemannianIsometry (n := n) (k := n)
        (ℝ ∙ (p : E)).reflection,
      isGeodesicSymmetryAt_unitSphereReflection p⟩

end Sphere

/-! ### Real hyperbolic space (upper half-space model) -/

section UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In the upper half-space model of real hyperbolic space, the composite of unit inversion about
`(0, 0)` with horizontal negation `(x, t) ↦ (-x, t)` is a geodesic symmetry at `(0, 1)`. -/
theorem isGeodesicSymmetryAt_upperHalfSpace_base :
    IsGeodesicSymmetryAt (I := 𝓘(ℝ, WithLp 2 (E × ℝ)))
      (UpperHalfSpace.inversion (E := E) 0 1 one_ne_zero *
        UpperHalfSpace.similarity 1 one_pos (LinearIsometryEquiv.neg ℝ) 0)
      (UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp)) := by
  let p₀ : UpperHalfSpace E := UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp)
  let S : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E) :=
    UpperHalfSpace.similarity 1 one_pos (LinearIsometryEquiv.neg ℝ) 0
  let J : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E) :=
    UpperHalfSpace.inversion 0 1 one_ne_zero
  have hp₀_coe : (p₀ : WithLp 2 (E × ℝ)) = WithLp.toLp 2 (0, 1) := UpperHalfSpace.coe_mk _ _
  have hp₀_height : UpperHalfSpace.height p₀ = 1 := UpperHalfSpace.height_mk _ _
  have hp₀_norm : ‖(p₀ : WithLp 2 (E × ℝ))‖ = 1 := by
    have hsq : ‖(p₀ : WithLp 2 (E × ℝ))‖ ^ 2 = 1 := by
      rw [hp₀_coe, WithLp.prod_norm_sq_eq_of_L2]
      simp
    nlinarith [norm_nonneg (p₀ : WithLp 2 (E × ℝ))]
  have hS_p₀ : S p₀ = p₀ := by
    apply UpperHalfSpace.ext_fst_height
    · simp [S, hp₀_coe]
    · simp [S, hp₀_height]
  have hJ_p₀ : J p₀ = p₀ := by
    apply UpperHalfSpace.ext
    rw [UpperHalfSpace.coe_inversion_apply, Prod.mk_zero_zero, WithLp.toLp_zero]
    simp [EuclideanGeometry.inversion_def, dist_zero_right, hp₀_norm]
  have hS_mul : S * S = 1 := by
    dsimp only [S]
    rw [UpperHalfSpace.similarity_mul_similarity]
    have hneg : (LinearIsometryEquiv.neg ℝ (E := E)).trans (LinearIsometryEquiv.neg ℝ) =
        LinearIsometryEquiv.refl ℝ E := by
      ext x
      simp
    simp [hneg]
  have hSJ_comm : S * J = J * S := by
    refine RiemannianIsometry.ext fun x ↦ ?_
    have hS_dist :
        dist (WithLp.toLp 2 (-(x : WithLp 2 (E × ℝ)).fst, x.height)) (WithLp.toLp 2 (0, 0)) =
          dist (x : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (0, 0)) := by
      rw [Prod.mk_zero_zero, WithLp.toLp_zero, dist_zero_right, dist_zero_right]
      have h1 : ‖WithLp.toLp 2 (-(x : WithLp 2 (E × ℝ)).fst, x.height)‖ ^ 2 =
          ‖(x : WithLp 2 (E × ℝ))‖ ^ 2 := by
        simp [WithLp.prod_norm_sq_eq_of_L2, UpperHalfSpace.snd_coe]
      nlinarith [norm_nonneg (WithLp.toLp 2 (-(x : WithLp 2 (E × ℝ)).fst, x.height)),
        norm_nonneg (x : WithLp 2 (E × ℝ))]
    apply UpperHalfSpace.ext_fst_height
    · simp [S, J, RiemannianIsometry.mul_apply, UpperHalfSpace.coe_inversion_apply,
        EuclideanGeometry.inversion_def, hS_dist]
    · simp [S, J, RiemannianIsometry.mul_apply, UpperHalfSpace.height_inversion_apply, hS_dist]
  refine ⟨?_, ?_, ?_⟩
  · rw [RiemannianIsometry.mul_apply, hS_p₀, hJ_p₀]
  · calc
      (J * S) * (J * S) = J * (S * J) * S := by group
      _ = J * (J * S) * S := by rw [hSJ_comm]
      _ = (J * J) * (S * S) := by group
      _ = 1 := by rw [UpperHalfSpace.inversion_mul_self, hS_mul, mul_one]
  · rw [RiemannianIsometry.coe_mul,
      mfderiv_comp p₀ (J.mdifferentiableAt (S p₀)) (S.mdifferentiableAt p₀)]
    ext v
    have hstep : ∀ {q : UpperHalfSpace E} (_ : q = p₀)
        (w : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) q)
        (w' : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) p₀),
        (w : WithLp 2 (E × ℝ)) = w' →
        tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (J q)
          (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) J q w) =
        tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (J p₀)
          (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) J p₀ w') := by
      rintro q rfl w _ rfl
      rfl
    have hSv : tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (S p₀)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) S p₀ v) =
        WithLp.toLp 2 (-(v : WithLp 2 (E × ℝ)).fst, (v : WithLp 2 (E × ℝ)).snd) := by
      rw [UpperHalfSpace.tangentSpaceCastModel_mfderiv_similarity, one_smul]
      refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_)
      · simp [LinearIsometryEquiv.withLpProdCongr_apply]
        rfl
      · simp [LinearIsometryEquiv.withLpProdCongr_apply]
        rfl
    have hJS : tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (J (S p₀))
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) J (S p₀)
          (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) S p₀ v)) =
        -(tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) p₀ v) := by
      let w' : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) p₀ :=
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) p₀).symm
          (WithLp.toLp 2 (-(v : WithLp 2 (E × ℝ)).fst, (v : WithLp 2 (E × ℝ)).snd))
      have hw' : (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) S p₀ v :
          WithLp 2 (E × ℝ)) = w' := hSv
      rw [hstep hS_p₀ _ w' hw', UpperHalfSpace.tangentSpaceCastModel_mfderiv_inversion]
      have hdist : dist (p₀ : WithLp 2 (E × ℝ)) (WithLp.toLp 2 (0, 0)) = 1 := by
        rw [Prod.mk_zero_zero, WithLp.toLp_zero, dist_zero_right, hp₀_norm]
      have hsub : (p₀ : WithLp 2 (E × ℝ)) - WithLp.toLp 2 (0, 0) = WithLp.toLp 2 (0, 1) := by
        rw [hp₀_coe, Prod.mk_zero_zero, WithLp.toLp_zero, sub_zero]
      rw [hdist, div_one, one_pow, one_smul, hsub, Submodule.reflection_orthogonal_apply,
        Submodule.reflection_singleton_apply]
      have hnorm01 : ‖WithLp.toLp 2 ((0 : E), (1 : ℝ))‖ = 1 := by rwa [← hp₀_coe]
      have hinner01 :
          inner ℝ (WithLp.toLp 2 ((0 : E), (1 : ℝ)))
            (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) p₀ w') =
          (v : WithLp 2 (E × ℝ)).snd := by
        simp [w', WithLp.prod_inner_apply]
      rw [hnorm01, hinner01]
      simp only [RCLike.ofReal_real_eq_id, id_eq, one_pow, div_one]
      refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_)
      · simp [w']
        rfl
      · simp [w', two_smul]
        rfl
    exact hJS

/-- Every upper half-space model of real hyperbolic space is a Riemannian symmetric space. -/
instance instIsRiemannianSymmetricSpaceUpperHalfSpace :
    IsRiemannianSymmetricSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E) :=
  isRiemannianSymmetricSpace_of_isPretransitive isGeodesicSymmetryAt_upperHalfSpace_base

end UpperHalfSpace

/-! ### The round unit circle and the flat 2-torus -/

section CircleAndTorus

private local instance circleFinrankFact : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
  ⟨by norm_num [Complex.finrank_real_complex]⟩

/-- The tautological diffeomorphism between the unit sphere in `ℂ` and `Circle`. -/
private def sphereComplexToCircleDiffeomorph :
    Diffeomorph (𝓡 1) (𝓡 1) (sphere (0 : ℂ) 1) Circle ∞ where
  toEquiv :=
    { toFun := fun z ↦ z
      invFun := fun z ↦ z
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id

/-- The tautological Riemannian isometry between the unit sphere in `ℂ` and `Circle` equipped with
`TauCeti.roundMetricCircle`. -/
private def sphereComplexToCircleIsometry :
    letI := TauCeti.roundMetricCircle
    RiemannianIsometry (𝓡 1) (𝓡 1) (sphere (0 : ℂ) 1) Circle :=
  letI := TauCeti.roundMetricCircle
  { toDiffeomorph := sphereComplexToCircleDiffeomorph
    inner_mfderiv' := fun x v w ↦ by
      rw [Circle.roundMetricCircle_inner, inner_tangentSpace_sphere,
        mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
      have hι : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ))
          (sphereComplexToCircleDiffeomorph x) :=
        (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x).mdifferentiableAt one_ne_zero
      have hφ : MDifferentiableAt (𝓡 1) (𝓡 1) sphereComplexToCircleDiffeomorph x :=
        sphereComplexToCircleDiffeomorph.contMDiff.mdifferentiable (by simp) x
      have hcomp := mfderiv_comp x hι hφ
      have hval : (fun z : Circle ↦ (z : ℂ)) ∘ sphereComplexToCircleDiffeomorph =
          (fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ)) := rfl
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp, hval]
      rfl }

/-- The unit circle equipped with its round metric is a Riemannian symmetric space. -/
theorem isRiemannianSymmetricSpace_circle :
    letI := TauCeti.roundMetricCircle
    IsRiemannianSymmetricSpace (𝓡 1) Circle :=
  letI := TauCeti.roundMetricCircle
  sphereComplexToCircleIsometry.isRiemannianSymmetricSpace

/-- The flat 2-torus `Circle × Circle` equipped with the product of round circle metrics is a
Riemannian symmetric space. -/
theorem isRiemannianSymmetricSpace_circle_prod :
    letI := TauCeti.roundMetricCircle
    IsRiemannianSymmetricSpace ((𝓡 1).prod (𝓡 1)) (Circle × Circle) :=
  letI := TauCeti.roundMetricCircle
  letI := isRiemannianSymmetricSpace_circle
  instIsRiemannianSymmetricSpaceProd

end CircleAndTorus

/-! ### Negative control I: proper open subsets of Euclidean space -/

section ProperOpenEuclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every open subset of a finite-dimensional real inner product space, carrying the restricted
Euclidean metric, has parallel curvature (it is flat, hence locally symmetric). -/
theorem hasParallelCurvature_opens_innerProductSpace (U : Opens F) :
    (leviCivitaConnection 𝓘(ℝ, F) U).HasParallelCurvature :=
  (IsLocalRiemannianIsometry.subtype_val (I := 𝓘(ℝ, F)) U).hasParallelCurvature
    (hasParallelCurvature_of_curvatureTensor_eq_zero _
      (curvatureTensor_leviCivitaConnection_model_space (F := F)))

/-- No nonempty proper open subset of a finite-dimensional real inner product space is a Riemannian
symmetric space, since any geodesic symmetry at every point forces geodesic completeness. -/
theorem not_isRiemannianSymmetricSpace_opens_innerProductSpace {U : Opens F}
    (hne : (U : Set F).Nonempty) (htop : U ≠ ⊤) :
    ¬ IsRiemannianSymmetricSpace 𝓘(ℝ, F) U := by
  intro hsym
  obtain ⟨x, hx⟩ := hne
  have hnotall : ¬ ∀ y : F, y ∈ U := fun hall ↦ htop (Opens.ext (Set.eq_univ_of_forall hall))
  push Not at hnotall
  obtain ⟨y, hy⟩ := hnotall
  let p : U := ⟨x, hx⟩
  let w : TangentSpace 𝓘(ℝ, F) (p : F) :=
    (tangentSpaceCastModel 𝓘(ℝ, F) (p : F)).symm (y - x)
  let v : TangentSpace 𝓘(ℝ, F) p := (tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) p).symm w
  have hcomp : IsGeodesicallyCompleteAt 𝓘(ℝ, F) U p :=
    isGeodesicallyCompleteAt_of_isRiemannianSymmetricSpace p
  have hexp := (IsLocalRiemannianIsometry.subtype_val (I := 𝓘(ℝ, F)) U).riemannianExp_mfderiv
    hcomp v
  rw [Manifold.mfderiv_subtype_val] at hexp
  dsimp only [v] at hexp
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    riemannianExp_model_space] at hexp
  have hy_eq : (riemannianExp 𝓘(ℝ, F) U p v : F) = y := by
    rw [← hexp]
    change x + (y - x) = y
    abel
  exact hy (hy_eq ▸ (riemannianExp 𝓘(ℝ, F) U p v).2)

/-- Punctured Euclidean space `F \ {x₀}` is flat (hence has parallel curvature) but is not a
Riemannian symmetric space. -/
theorem not_isRiemannianSymmetricSpace_compl_singleton [Nontrivial F] (x₀ : F) :
    ¬ IsRiemannianSymmetricSpace 𝓘(ℝ, F)
        (⟨{x : F | x ≠ x₀}, isOpen_ne⟩ : Opens F) := by
  obtain ⟨x, hx⟩ := exists_ne x₀
  refine not_isRiemannianSymmetricSpace_opens_innerProductSpace ⟨x, hx⟩ ?_
  intro htop
  have : x₀ ∈ (⟨{x : F | x ≠ x₀}, isOpen_ne⟩ : Opens F) := by
    rw [htop]
    trivial
  exact this rfl

end ProperOpenEuclidean

/-! ### Negative control II: complete simply connected warped planes -/

section WarpedPlane

/-- The warped product metric `dx² + f(x)² dy²` on `ℝ × ℝ`, for a smooth nowhere-vanishing
warping function `f : ℝ → ℝ`. -/
def warpedPlaneMetric (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0) :
    ContMDiffRiemannianMetric (𝓘(ℝ).prod 𝓘(ℝ)) ∞ (ℝ × ℝ)
      (fun p : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) p) :=
  ((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).warpedProdTangentSpace
    f hf.contMDiff hf₀ ((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top)

/-- The scalar curvature of `dx² + f(x)² dy²` on `ℝ × ℝ` is `-2 f''(x) / f(x)`. -/
theorem scalarCurvature_warpedPlaneMetric (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hf₀ : ∀ x, f x ≠ 0) (p : ℝ × ℝ) :
    (warpedPlaneMetric f hf hf₀).scalarCurvature p = -2 * deriv (deriv f) p.1 / f p.1 := by
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  have hg : g.scalarCurvature p.1 = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection g
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm,
      scalarCurvature_leviCivitaConnection_model_space]
  have hg₂ : g.scalarCurvature p.2 = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection g
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _).symm,
      scalarCurvature_leviCivitaConnection_model_space]
  have hgrad : DifferentiableAt ℝ (gradient f) p.1 :=
    (hf.gradient_right (m := 1) (by simp)).differentiable (by simp) p.1
  have hlap :
      (letI : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ) x) :=
        ⟨g.toRiemannianMetric⟩
      laplaceBeltrami 𝓘(ℝ) f p.1) = deriv (deriv f) p.1 := by
    let : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ) x) := ⟨g.toRiemannianMetric⟩
    rw [laplaceBeltrami_eq_laplacian_of_eq
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofLE _ _) hgrad,
      InnerProductSpace.laplacian_eq_iteratedDeriv_real]
    simp [iteratedDeriv_succ]
  dsimp only [warpedPlaneMetric]
  rw [ContMDiffRiemannianMetric.scalarCurvature_warpedProdTangentSpace, hg, hg₂, hlap]
  simp only [Module.finrank_self, Nat.cast_one, sub_self, zero_div, add_zero, mul_one]
  ring

/-- `WithMetric (warpedPlaneMetric f hf hf₀)` is contractible (hence simply connected). -/
instance instContractibleSpaceWithMetricWarpedPlane (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hf₀ : ∀ x, f x ≠ 0) :
    ContractibleSpace (WithMetric (warpedPlaneMetric f hf hf₀)) :=
  (WithMetric.homeomorph (warpedPlaneMetric f hf hf₀)).contractibleSpace

/-- If `f : ℝ → ℝ` is bounded away from zero (`0 < c` and `c ≤ |f x|` for all `x`), then
`(ℝ × ℝ, dx² + f(x)² dy²)` is geodesically complete at every point. -/
theorem isGeodesicallyCompleteAt_withMetric_warpedPlaneMetric (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x, c ≤ |f x|)
    (p : WithMetric (warpedPlaneMetric f hf hf₀)) :
    IsGeodesicallyCompleteAt (𝓘(ℝ).prod 𝓘(ℝ))
      (WithMetric (warpedPlaneMetric f hf hf₀)) p := by
  have : IsContinuousRiemannianBundle (ℝ × ℝ)
      (fun x : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := 𝓘(ℝ).prod 𝓘(ℝ)) (n := ∞) (F := ℝ × ℝ)
      (V := fun x : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x)
  let g := warpedPlaneMetric f hf hf₀
  let : EMetricSpace (WithMetric g) := .ofRiemannianMetric (𝓘(ℝ).prod 𝓘(ℝ)) (WithMetric g)
  let m : MetricSpace (ℝ × ℝ) :=
    MetricSpace.ofRiemannianMetric (𝓘(ℝ).prod 𝓘(ℝ)) (ℝ × ℝ)
  have hcm : @CompleteSpace (ℝ × ℝ) m.toUniformSpace :=
    completeSpace_ofRiemannianMetric_of_isRiemannianSymmetricSpace
      (I := 𝓘(ℝ).prod 𝓘(ℝ)) (M := ℝ × ℝ)
  let C : ℝ≥0 := max 1 ⟨c⁻¹, inv_nonneg.2 hc.le⟩
  have hC1 : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast le_max_left (1 : ℝ≥0) ⟨c⁻¹, inv_nonneg.2 hc.le⟩
  have hCinv : c⁻¹ ≤ (C : ℝ) := by
    exact_mod_cast le_max_right (1 : ℝ≥0) ⟨c⁻¹, inv_nonneg.2 hc.le⟩
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0] at hC1
    norm_num at hC1
  have hdom : ∀ x (v : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x),
      ‖v‖ ^ 2 ≤ (C : ℝ) ^ 2 * g.inner x v v := fun x v ↦ by
    rw [← real_inner_self_eq_norm_sq, Manifold.inner_tangentSpace_prod]
    dsimp only [g, warpedPlaneMetric]
    rw [ContMDiffRiemannianMetric.warpedProdTangentSpace_inner,
      ContMDiffRiemannianMetric.ofLE_inner]
    set u := tangentSpaceProdEquiv x v
    have h1 : (1 : ℝ) ≤ (C : ℝ) ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ (C : ℝ) ^ 2 * f x.1 ^ 2 := by
      have hcf : 1 ≤ (C : ℝ) * |f x.1| := calc
        (1 : ℝ) = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
        _ ≤ (C : ℝ) * |f x.1| := mul_le_mul hCinv (hbound x.1) hc.le (by positivity)
      have hsq : (1 : ℝ) ^ 2 ≤ ((C : ℝ) * |f x.1|) ^ 2 :=
        pow_le_pow_left₀ zero_le_one hcf 2
      simpa [mul_pow, sq_abs] using hsq
    have hu1 : (riemannianMetricVectorSpace ℝ).inner x.1 u.1 u.1 = inner ℝ u.1 u.1 := rfl
    have hu2 : (riemannianMetricVectorSpace ℝ).inner x.2 u.2 u.2 = inner ℝ u.2 u.2 := rfl
    rw [hu1, hu2]
    nlinarith [real_inner_self_nonneg (x := u.1), real_inner_self_nonneg (x := u.2)]
  have hlip : @LipschitzWith (WithMetric g) (ℝ × ℝ) _ m.toPseudoEMetricSpace C
      WithMetric.ofWithMetric := fun x y ↦
    WithMetric.riemannianEDist_ofWithMetric_le_mul hC0 hdom x y
  have huc : @UniformContinuous (WithMetric g) (ℝ × ℝ) _ m.toUniformSpace
      WithMetric.ofWithMetric :=
    @LipschitzWith.uniformContinuous (WithMetric g) (ℝ × ℝ) _ m.toPseudoEMetricSpace _ _ hlip
  have : CompleteSpace (WithMetric g) :=
    @CompleteSpace.of_comp_eq_id (ℝ × ℝ) (WithMetric g) m.toUniformSpace _
      (WithMetric.toWithMetric g) WithMetric.ofWithMetric rfl
      WithMetric.continuous_toWithMetric huc hcm
  exact isGeodesicallyCompleteAt_of_completeSpace p

/-- If `f'' / f` is nonconstant, then `(ℝ × ℝ, dx² + f(x)² dy²)` does not have parallel
curvature. -/
theorem not_hasParallelCurvature_withMetric_warpedPlaneMetric (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0) {x₁ x₂ : ℝ}
    (hne : deriv (deriv f) x₁ / f x₁ ≠ deriv (deriv f) x₂ / f x₂) :
    ¬ (leviCivitaConnection (𝓘(ℝ).prod 𝓘(ℝ))
        (WithMetric (warpedPlaneMetric f hf hf₀))).HasParallelCurvature := by
  intro hpar
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hloc :=
    (hasParallelCurvature_iff_isLocallyConstant_scalarCurvature_of_finrank_eq_two
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod 𝓘(ℝ))) hdim).1 hpar
  let g := warpedPlaneMetric f hf hf₀
  have hscal : ∀ q : WithMetric g,
      (leviCivitaConnection (𝓘(ℝ).prod 𝓘(ℝ)) (WithMetric g)).scalarCurvature q =
        g.scalarCurvature q.ofWithMetric := fun q ↦ by
    let : RiemannianBundle (fun x : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) x) :=
      ⟨g.toRiemannianMetric⟩
    have hl : IsLocalRiemannianIsometry (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ))
        (WithMetric.ofWithMetric : WithMetric g → ℝ × ℝ) :=
      { contMDiff := WithMetric.contMDiff_ofWithMetric
        isInvertible_mfderiv := fun z ↦ by
          rw [WithMetric.mfderiv_ofWithMetric]
          exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
        inner_mfderiv := fun z u v ↦ (WithMetric.inner_def z u v).symm }
    rw [ContMDiffRiemannianMetric.scalarCurvature_def g q.ofWithMetric]
    exact (hl.scalarCurvature_map q).symm
  have heq := hloc.apply_eq_of_preconnectedSpace
    (WithMetric.toWithMetric g (x₁, 0)) (WithMetric.toWithMetric g (x₂, 0))
  rw [hscal, hscal, WithMetric.ofWithMetric_toWithMetric, WithMetric.ofWithMetric_toWithMetric,
    scalarCurvature_warpedPlaneMetric, scalarCurvature_warpedPlaneMetric] at heq
  apply hne
  rw [mul_div_assoc, mul_div_assoc] at heq
  exact mul_left_cancel₀ (by norm_num) heq

/-- If `f'' / f` is nonconstant, then `(ℝ × ℝ, dx² + f(x)² dy²)` is not a Riemannian
symmetric space. -/
theorem not_isRiemannianSymmetricSpace_withMetric_warpedPlaneMetric (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hf₀ : ∀ x, f x ≠ 0) {x₁ x₂ : ℝ}
    (hne : deriv (deriv f) x₁ / f x₁ ≠ deriv (deriv f) x₂ / f x₂) :
    ¬ IsRiemannianSymmetricSpace (𝓘(ℝ).prod 𝓘(ℝ))
        (WithMetric (warpedPlaneMetric f hf hf₀)) := by
  intro hsym
  exact not_hasParallelCurvature_withMetric_warpedPlaneMetric f hf hf₀ hne
    (hasParallelCurvature_leviCivitaConnection_of_isRiemannianSymmetricSpace
      (I := 𝓘(ℝ).prod 𝓘(ℝ)) (M := WithMetric (warpedPlaneMetric f hf hf₀)))

/-- Concrete negative control: `ℝ × ℝ` with the warped metric `dx² + (x² + 1)² dy²` is
simply connected and geodesically complete at every point, yet is not a Riemannian symmetric
space. -/
theorem exists_complete_simplyConnected_not_isRiemannianSymmetricSpace :
    ∃ g : ContMDiffRiemannianMetric (𝓘(ℝ).prod 𝓘(ℝ)) ∞ (ℝ × ℝ)
        (fun p : ℝ × ℝ ↦ TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) p),
      SimplyConnectedSpace (WithMetric g) ∧
      (∀ p : WithMetric g,
        IsGeodesicallyCompleteAt (𝓘(ℝ).prod 𝓘(ℝ)) (WithMetric g) p) ∧
      ¬ IsRiemannianSymmetricSpace (𝓘(ℝ).prod 𝓘(ℝ)) (WithMetric g) := by
  let f : ℝ → ℝ := fun x ↦ x ^ 2 + 1
  have hf : ContDiff ℝ ∞ f := (contDiff_id.pow 2).add contDiff_const
  have hf₀ : ∀ x : ℝ, f x ≠ 0 := fun x ↦ by dsimp [f]; positivity
  refine ⟨warpedPlaneMetric f hf hf₀, inferInstance,
    isGeodesicallyCompleteAt_withMetric_warpedPlaneMetric f hf hf₀ one_pos (fun x ↦ by
      rw [abs_of_pos (by dsimp [f]; positivity)]
      dsimp [f]
      nlinarith),
    not_isRiemannianSymmetricSpace_withMetric_warpedPlaneMetric f hf hf₀
      (x₁ := 0) (x₂ := 1) ?_⟩
  have hderiv : deriv f = fun x : ℝ ↦ 2 * x := by
    funext x
    have h : HasDerivAt f ((2 : ℕ) * x ^ (2 - 1) * 1) x :=
      ((hasDerivAt_id x).pow 2).add_const 1
    rw [h.deriv]
    ring
  have hdderiv : ∀ x : ℝ, deriv (deriv f) x = 2 := fun x ↦ by
    rw [hderiv]
    have h : HasDerivAt (fun t : ℝ ↦ 2 * t) (2 * 1) x := (hasDerivAt_id x).const_mul 2
    rw [h.deriv]
    ring
  rw [hdderiv 0, hdderiv 1]
  norm_num [f]

end WarpedPlane

end TauCeti
