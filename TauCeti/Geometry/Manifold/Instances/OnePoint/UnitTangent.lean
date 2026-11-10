/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Manifold.Instances.Stiefel.UnitTangent
public import TauCeti.Geometry.Manifold.Diffeomorph.Tangent

/-!
# The unit tangent bundle of the Riemann sphere is `SO(3)`

The round metric of the Riemann sphere `OnePoint ℂ` is `4π` times its Fubini–Study metric,
`g(a, b) = 4π ω_FS(a, i b)`, where `ω_FS` (`OnePoint.fubiniStudyForm`) is normalized to total area
one: it is the metric pulled back from the round unit sphere `S²` along the diffeomorphism
`σ = OnePoint.diffeomorphSphere v ι` (`OnePoint.inner_mfderiv_diffeomorphSphere`). Its unit
tangent bundle is the set of tangent vectors `a` with `4π ω_FS(a, i a) = 1` in the tangent bundle
`TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)` of the Riemann sphere, regarded as a real surface.

This file transports the identification of the unit tangent bundle of the round sphere `S²` with
`SO(3)` (`TauCeti.sphereUnitTangentHomeomorphSpecialOrthogonalGroup`) to the Riemann sphere. The
tangent map of `σ` is a homeomorphism of tangent bundles carrying the unit tangent vectors of the
Riemann sphere onto those of `S²` (`OnePoint.unitTangentHomeomorphSphere`). Composing, a unit
tangent vector `a` at `x` goes to the rotation whose columns are the oriented orthonormal frame
`(σ x, dσ a, σ x ⨯₃ dσ a)` of `ℝ³` (`OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup`).

## Main definitions

* `OnePoint.unitTangentHomeomorphSphere v ι`: the tangent map of `σ` identifies the unit tangent
  bundle of the Riemann sphere for its round metric with that of the round sphere `S²`.
* `OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup v ι`: the unit tangent bundle of the
  Riemann sphere for its round metric is homeomorphic to `SO(3)`.

## Main results

* `OnePoint.norm_mfderiv_diffeomorphSphere_sq`: `‖dσ a‖² = 4π ω_FS(a, i a)`.
* `OnePoint.coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply`: the rotation attached to a
  unit tangent vector.
* `OnePoint.proj_unitTangentHomeomorphSpecialOrthogonalGroup_symm_apply`: the base point of the
  unit tangent vector attached to a rotation `A` is the point of the Riemann sphere sent by `σ` to
  the first column of `A`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (stereographic coordinates on the round sphere).
-/

public section

open Bundle Matrix Metric Module WithLp TauCeti TauCeti.Matrix.SpecialOrthogonalGroup
open scoped Manifold TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]
  (v : sphere (0 : E) 1) (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ)

/-- **The round norm on the Riemann sphere.** The round norm of the image of a tangent vector `a`
of the Riemann sphere under the differential of `σ = diffeomorphSphere v ι` is given by
`‖dσ a‖² = 4π ω_FS(a, i a)`. -/
theorem norm_mfderiv_diffeomorphSphere_sq (x : OnePoint ℂ) (a : ℂ) :
    ‖mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x a‖ ^ 2 =
      4 * Real.pi * SmoothBundleForm.eval₂ fubiniStudyForm x a (Complex.I * a) := by
  rw [← real_inner_self_eq_norm_sq, inner_mfderiv_diffeomorphSphere]

/-- **The unit tangent bundle of the Riemann sphere is that of the round sphere.** The tangent map
of `σ = diffeomorphSphere v ι` carries the tangent vectors `a` of the Riemann sphere with
`4π ω_FS(a, i a) = 1`, the unit vectors of its round metric, onto the unit tangent vectors of the
round sphere `S²`. -/
def unitTangentHomeomorphSphere :
    {p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ) | 4 * Real.pi *
        SmoothBundleForm.eval₂ fubiniStudyForm p.proj p.2 (Complex.I * (id p.2 : ℂ)) = 1} ≃ₜ
      {q : TangentBundle (𝓡 2) (sphere (0 : E) 1) | ‖q.2‖ = 1} :=
  ((diffeomorphSphere v ι).tangentHomeomorph (by simp)).subtype fun p ↦ by
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Diffeomorph.coe_tangentHomeomorph]
    -- The fibre component of the tangent map at `p` is `dσ p.2`.
    change _ ↔ ‖mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) p.proj p.2‖ = 1
    rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, one_pow]
    exact (congrArg (· = (1 : ℝ)) (norm_mfderiv_diffeomorphSphere_sq v ι p.proj p.2)).symm.to_iff

/-- The unit tangent vector `a` at `x` goes to the unit tangent vector `dσ a` at `σ x`. -/
@[simp]
theorem coe_unitTangentHomeomorphSphere_apply
    (p : {p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ) | 4 * Real.pi *
      SmoothBundleForm.eval₂ fubiniStudyForm p.proj p.2 (Complex.I * (id p.2 : ℂ)) = 1}) :
    (unitTangentHomeomorphSphere v ι p : TangentBundle (𝓡 2) (sphere (0 : E) 1)) =
      tangentMap 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) p :=
  by simp [unitTangentHomeomorphSphere]

/-- The inverse sends the unit tangent vector `w` at `y` to `(dσ)⁻¹ w` at `σ⁻¹ y`. -/
@[simp]
theorem coe_unitTangentHomeomorphSphere_symm_apply
    (q : {q : TangentBundle (𝓡 2) (sphere (0 : E) 1) | ‖q.2‖ = 1}) :
    ((unitTangentHomeomorphSphere v ι).symm q : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)) =
      tangentMap (𝓡 2) 𝓘(ℝ, ℂ) (diffeomorphSphere v ι).symm q :=
  by simp [unitTangentHomeomorphSphere]

end Sphere

section SpecialOrthogonalGroup

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

variable (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin 3)))ᗮ)

/-- **The unit tangent bundle of the Riemann sphere is `SO(3)`.** A tangent vector `a` of the
Riemann sphere at `x` with `4π ω_FS(a, i a) = 1`, a unit vector for its round metric, goes to the
rotation whose columns are the oriented orthonormal frame `(σ x, dσ a, σ x ⨯₃ dσ a)` of `ℝ³`, where
`σ = diffeomorphSphere v ι` and `dσ a` is read in `ℝ³`. -/
def unitTangentHomeomorphSpecialOrthogonalGroup :
    {p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ) | 4 * Real.pi *
        SmoothBundleForm.eval₂ fubiniStudyForm p.proj p.2 (Complex.I * (id p.2 : ℂ)) = 1} ≃ₜ
      specialOrthogonalGroup (Fin 3) ℝ :=
  (unitTangentHomeomorphSphere v ι).trans sphereUnitTangentHomeomorphSpecialOrthogonalGroup

/-- The rotation attached to the unit tangent vector `a` at `x` has columns `σ x`, `dσ a` and
`σ x ⨯₃ dσ a`, with `dσ a` read in `ℝ³` through the differential of the inclusion of the sphere. -/
@[simp]
theorem coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply
    (p : {p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ) | 4 * Real.pi *
      SmoothBundleForm.eval₂ fubiniStudyForm p.proj p.2 (Complex.I * (id p.2 : ℂ)) = 1}) :
    (unitTangentHomeomorphSpecialOrthogonalGroup v ι p : Matrix (Fin 3) (Fin 3) ℝ) =
      ofFrame (ofLp (diffeomorphSphere v ι p.1.proj : EuclideanSpace ℝ (Fin 3)))
        (ofLp (mvfderiv (𝓡 2)
          ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
          (diffeomorphSphere v ι p.1.proj)
          (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) p.1.proj p.1.2))) := by
  simp only [unitTangentHomeomorphSpecialOrthogonalGroup, Homeomorph.trans_apply,
    coe_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_apply]
  -- The base point and the fibre component both depend on the image of `p`, so rewrite it as a
  -- whole: it is the tangent map of `σ` at `p`, whose fibre component is `dσ a` by definition.
  generalize hq : (unitTangentHomeomorphSphere v ι p).1 = q
  rw [coe_unitTangentHomeomorphSphere_apply] at hq
  subst hq
  rfl

/-- The unit tangent vector attached to a rotation `A` lies over the point of the Riemann sphere
sent by `σ` to the first column of `A`. -/
@[simp]
theorem proj_unitTangentHomeomorphSpecialOrthogonalGroup_symm_apply
    (A : specialOrthogonalGroup (Fin 3) ℝ) :
    diffeomorphSphere v ι ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).symm A).1.proj =
      toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 0) := by
  have h := congr_arg (fun B : specialOrthogonalGroup (Fin 3) ℝ ↦
    ((B : Matrix (Fin 3) (Fin 3) ℝ).col 0))
    ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).apply_symm_apply A)
  simp only [coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply, ofFrame_col_zero] at h
  rw [← h, toLp_ofLp]

end SpecialOrthogonalGroup

end OnePoint
