/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import TauCeti.Geometry.Manifold.Riemannian.Circle
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.UpperHalfSpace
public import TauCeti.Geometry.Manifold.Riemannian.Symmetric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.WarpedProd.Plane
import TauCeti.Geometry.Manifold.MFDeriv.Congr
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction

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
* **Proper open subsets of Euclidean space** (in particular punctured Euclidean space `F \ {x₀}`):
  although every open subset of a finite-dimensional real inner product space has parallel
  curvature (`TauCeti.hasParallelCurvature_opens_innerProductSpace`), no nonempty proper open
  subset is a Riemannian symmetric space because it is not geodesically complete.
* **Complete simply connected surfaces of nonconstant curvature**: on `ℝ × ℝ`, the warped plane
  `TauCeti.warpedPlaneMetric f hf hf₀` (`dx² + f(x)² dy²`) is simply connected and, when `|f|` is
  bounded away from zero, geodesically complete; when `f'' / f` is nonconstant (for example
  `f(x) = x² + 1`), it fails to have parallel curvature and is therefore not a Riemannian symmetric
  space.

## Main results

* `TauCeti.isGeodesicSymmetryAt_pointReflection` and
  `TauCeti.instIsRiemannianSymmetricSpaceInnerProductSpace`: every real inner product space is a
  Riemannian symmetric space.
* `TauCeti.isGeodesicSymmetryAt_unitSphereReflection` and
  `TauCeti.instIsRiemannianSymmetricSpaceSphere`: every round unit sphere is a Riemannian
  symmetric space.
* `TauCeti.isGeodesicSymmetryAt_upperHalfSpace_base` and
  `TauCeti.instIsRiemannianSymmetricSpaceUpperHalfSpace`: every upper half-space model of real
  hyperbolic space is a Riemannian symmetric space.
* `TauCeti.isRiemannianSymmetricSpace_circle` and
  `TauCeti.isRiemannianSymmetricSpace_circle_prod`: the round unit circle and the flat 2-torus are
  Riemannian symmetric spaces.
* `TauCeti.not_isRiemannianSymmetricSpace_opens_innerProductSpace` and
  `TauCeti.not_isRiemannianSymmetricSpace_compl_singleton`: nonempty proper open subsets of
  Euclidean space (including punctured space `F \ {x₀}`) are not Riemannian symmetric spaces.
* `TauCeti.not_isRiemannianSymmetricSpace_withMetric_warpedPlaneMetric` and
  `TauCeti.exists_complete_simplyConnected_not_isRiemannianSymmetricSpace`: warped planes with
  nonconstant `f'' / f` are not Riemannian symmetric spaces, instantiated for `f(x) = x² + 1`.

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
open scoped ContDiff InnerProductSpace Manifold TauCeti

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
    let Φ := LinearIsometryEquiv.unitSphereRiemannianIsometry (n := n) (k := n) e
    have hep : Φ p = p := by
      apply Subtype.ext
      rw [LinearIsometryEquiv.coe_unitSphereRiemannianIsometry_apply]
      exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self (p : E))
    refine eq_neg_id_of_apply hep fun v ↦ ?_
    have hcoe := LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv (n := n) (k := n) e p v
    rw [← LinearIsometryEquiv.coe_unitSphereRiemannianIsometry (n := n) (k := n)] at hcoe
    let w : TangentSpace (𝓡 n) p :=
      tangentSpaceCast (𝓡 n) (Φ p) p (mfderiv (𝓡 n) (𝓡 n) Φ p v)
    have hw : (mfderiv (𝓡 n) (𝓡 n) Φ p v : EuclideanSpace ℝ (Fin n)) = w :=
      (coe_tangentSpaceCast (𝓡 n) (Φ p) p (mfderiv (𝓡 n) (𝓡 n) Φ p v)).symm
    have hmv : mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p w =
        e (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) := by
      rw [mvfderiv_apply_eq_mfderiv_apply,
        ← mfderiv_apply_congr_point (f := (Subtype.val : sphere (0 : E) 1 → E)) hep hw,
        ← mvfderiv_apply_eq_mfderiv_apply]
      exact hcoe
    have horth :
        inner ℝ (p : E) (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) = 0 :=
      inner_coe_mvfderiv_subtypeVal_sphere p v
    have hrefl : e (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) =
        -(mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) p v) := by
      dsimp only [e]
      rw [Submodule.reflection_singleton_apply, horth, RCLike.ofReal_real_eq_id, id_eq, zero_div,
        zero_smul, smul_zero, zero_sub]
    have hw_eq : w = -v :=
      injective_mvfderiv_subtypeVal_sphere (n := n) p
        (hmv.trans (hrefl.trans (map_neg _ v).symm))
    exact hw.trans hw_eq

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
      (UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp)) where
  apply_eq := by
    rw [RiemannianIsometry.mul_apply, UpperHalfSpace.similarity_one_apply_zero_one,
      UpperHalfSpace.inversion_zero_one_apply_zero_one]
  mul_self := by
    let S := UpperHalfSpace.similarity 1 one_pos (LinearIsometryEquiv.neg ℝ (E := E)) 0
    let J := UpperHalfSpace.inversion (E := E) 0 1 one_ne_zero
    calc
      (J * S) * (J * S) = J * (S * J) * S := by group
      _ = J * (J * S) * S := by
        rw [UpperHalfSpace.similarity_one_comm_inversion_zero (LinearIsometryEquiv.neg ℝ)
          one_ne_zero]
      _ = (J * J) * (S * S) := by group
      _ = 1 := by
        rw [UpperHalfSpace.inversion_mul_self, UpperHalfSpace.similarity_neg_mul_self, mul_one]
  mfderiv_eq := by
    let p₀ : UpperHalfSpace E := UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp)
    let Φ : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E) :=
      UpperHalfSpace.inversion (E := E) 0 1 one_ne_zero *
        UpperHalfSpace.similarity 1 one_pos (LinearIsometryEquiv.neg ℝ) 0
    have hfix : Φ p₀ = p₀ := by
      rw [RiemannianIsometry.mul_apply, UpperHalfSpace.similarity_one_apply_zero_one,
        UpperHalfSpace.inversion_zero_one_apply_zero_one]
    refine eq_neg_id_of_tangentSpaceCastModel_apply hfix fun v ↦ ?_
    rw [UpperHalfSpace.tangentSpaceCastModel_mfderiv_inversion_zero_one_mul_similarity_one]
    refine (WithLp.ext_iff 2).2 (Prod.ext ?_ ?_) <;>
      simp [p₀, LinearIsometryEquiv.withLpProdCongr_apply]

/-- Every upper half-space model of real hyperbolic space is a Riemannian symmetric space. -/
instance instIsRiemannianSymmetricSpaceUpperHalfSpace :
    IsRiemannianSymmetricSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E) :=
  isRiemannianSymmetricSpace_of_isPretransitive isGeodesicSymmetryAt_upperHalfSpace_base

end UpperHalfSpace

/-! ### The round unit circle and the flat 2-torus -/

section CircleAndTorus

/-- The unit circle equipped with its round metric is a Riemannian symmetric space. -/
theorem isRiemannianSymmetricSpace_circle :
    letI := TauCeti.roundMetricCircle
    IsRiemannianSymmetricSpace (𝓡 1) Circle := by
  let := TauCeti.roundMetricCircle
  have : Fact (Module.finrank ℝ ℂ = 1 + 1) := Complex.finrank_real_complex_fact
  exact sphereComplexToCircleIsometry.isRiemannianSymmetricSpace

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
    (NormedSpace.fromTangentSpace (p : F)).symm (y - x)
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
    rw [← hexp, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  exact hy (hy_eq ▸ (riemannianExp 𝓘(ℝ, F) U p v).property)

/-- Punctured Euclidean space `F \ {x₀}` is not a Riemannian symmetric space; contrast
`TauCeti.hasParallelCurvature_opens_innerProductSpace`. -/
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

end
