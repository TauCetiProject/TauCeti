/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# The geodesic curvature of plane curves

In a finite-dimensional real inner-product space with its standard Riemannian metric the covariant
acceleration of a `C²` curve is its second derivative, so the signed geodesic curvature of `γ`
relative to a field `n` along it is the classical `k_g = ⟪γ'', n⟫ / ‖γ'‖²`. In particular straight
lines have zero geodesic curvature, and for `R > 0` the circle `circleMap c R` of radius `R` in `ℂ`
has geodesic curvature `1 / R` relative to the unit normal pointing to its centre.

## Main results

* `TauCeti.Manifold.geodesicCurvature_model_space`: the formula `k_g = ⟪γ'', n⟫ / ‖γ'‖²`.
* `TauCeti.Manifold.geodesicCurvature_add_smul`: an affine line has zero geodesic curvature.
* `TauCeti.Manifold.geodesicCurvature_circleMap`: the circle `circleMap c R` has geodesic curvature
  `R⁻¹` relative to the normal `-circleMap 0 1`.

## References

* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Prentice-Hall, 1976, §1-5
  and §4-4.
-/

public section

open Complex Manifold
open scoped ContDiff Manifold InnerProductSpace

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The geodesic curvature of a curve in an inner-product space** which is `C²` at `t` is
`⟪γ'', n⟫ / ‖γ'‖²`. -/
theorem geodesicCurvature_model_space {γ : ℝ → F} {t : ℝ} (hγ : ContDiffAt ℝ 2 γ t)
    (n : ℝ → F) :
    geodesicCurvature (I := 𝓘(ℝ, F)) γ n t = ⟪deriv (deriv γ) t, n t⟫_ℝ / ‖deriv γ t‖ ^ 2 := by
  refine (geodesicCurvature_def (I := 𝓘(ℝ, F)) γ n t).trans ?_
  rw [acceleration_model_space hγ, norm_tangentSpace_vectorSpace, curveVelocity_eq_deriv]
  rfl

/-- An affine line `s ↦ p + s • v` has zero geodesic curvature, relative to every normal. -/
@[simp]
theorem geodesicCurvature_add_smul (p v : F) (n : ℝ → F) (t : ℝ) :
    geodesicCurvature (I := 𝓘(ℝ, F)) (fun s : ℝ ↦ p + s • v) n t = 0 := by
  have hd : deriv (fun s : ℝ ↦ p + s • v) = fun _ ↦ v := by
    funext s
    simpa using ((hasDerivAt_id s).smul_const v).const_add p |>.deriv
  rw [geodesicCurvature_model_space (by fun_prop), hd, deriv_const', inner_zero_left, zero_div]

/-- The circle `circleMap c R` of centre `c` and radius `|R|` has geodesic curvature `R⁻¹` relative
to the unit normal `-circleMap 0 1`. For `R > 0` this normal points to the centre; for `R < 0` it
points away from the centre and the curvature `R⁻¹ = -1 / |R|` is negative. -/
@[simp]
theorem geodesicCurvature_circleMap (c : ℂ) (R θ : ℝ) :
    geodesicCurvature (I := 𝓘(ℝ, ℂ)) (circleMap c R) (fun θ ↦ -circleMap 0 1 θ) θ = R⁻¹ := by
  -- the speed is `|R|` and the acceleration is `-circleMap 0 R θ = -(R • circleMap 0 1 θ)`
  have hv : ‖deriv (circleMap c R) θ‖ = |R| := by simp
  have ha : deriv (deriv (circleMap c R)) θ = -(R • circleMap 0 1 θ) := by
    simp only [funext (deriv_circleMap c R)]
    rw [((hasDerivAt_circleMap 0 R θ).mul_const I).deriv, mul_assoc, I_mul_I, mul_neg_one]
    simp [circleMap_zero, real_smul]
  rw [geodesicCurvature_model_space (contDiff_circleMap c R).contDiffAt, hv, ha, inner_neg_neg,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [norm_circleMap_zero, abs_one, one_pow, mul_one, sq_abs]
  rw [sq, div_self_mul_self']

end TauCeti.Manifold
