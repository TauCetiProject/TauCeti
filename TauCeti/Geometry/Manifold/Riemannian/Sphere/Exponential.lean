/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar.Jacobian
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Compact
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The differential of the exponential map of the round sphere

The exponential map of the unit sphere `Sⁿ ⊆ E` at `p` is, in ambient coordinates,
`exp_p(v) = cos ‖v‖ p + (sin ‖v‖ / ‖v‖) v`, where `v` is read in `E` through the differential
of the inclusion (`TauCeti.coe_riemannianExp_sphere`).

Differentiating this formula at a nonzero `x` in a direction `h` orthogonal to `x` only
differentiates the coefficient of the linear term, because the norm is stationary along `h`:
`d(exp_p)_x(h) = (sin ‖x‖ / ‖x‖) h` in ambient coordinates. For `x = r v` and `h = r w`, with
`v` a unit vector and `w ⊥ v`, this has norm `|sin r| ‖w‖`: the angular Jacobian of geodesic
polar coordinates on the round sphere is `sin r`.

## Main results

* `TauCeti.mvfderiv_coe_mfderiv_riemannianExp_sphere_of_inner_eq_zero`: the ambient
  differential of the exponential map in a direction orthogonal to the base vector.
* `TauCeti.norm_mfderiv_riemannianExp_sphere_smul`: the norm `|sin r| ‖w‖` of the angular
  differential `d(exp_p)_(r v)(r w)`.
* `TauCeti.polarJacobian_sphere`: the polar Jacobian of the unit sphere is `|sin r|` on unit
  angular directions.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapter 5
  (geodesics of the round sphere) and Chapter 10 (Jacobi fields of constant curvature spaces).
-/

public section

open Bundle ContinuousLinearMap Metric Module Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

local notation "ι" => ((↑) : sphere (0 : E) 1 → E)

/-- In a direction orthogonal to a nonzero point of an inner product space, the function
`y ↦ cos ‖y‖ P + (sin ‖y‖ / ‖y‖) L y` differentiates only through its linear term. -/
private theorem hasFDerivAt_cos_norm_smul_add_sinc_smul_apply_of_inner_eq_zero {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (P : E) (L : F →L[ℝ] E) {x h : F}
    (hx : x ≠ 0) (hxh : ⟪x, h⟫_ℝ = 0) :
    ∃ D : F →L[ℝ] E,
      HasFDerivAt (fun y : F ↦ Real.cos ‖y‖ • P + (Real.sin ‖y‖ / ‖y‖) • L y) D x ∧
        D h = (Real.sin ‖x‖ / ‖x‖) • L h := by
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hN : HasFDerivAt (fun y : F ↦ ‖y‖)
      ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by positivity)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ by simp only [Real.sqrt_sq (norm_nonneg y)])
  set N' : F →L[ℝ] ℝ := (1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x) with hN'
  have hNh : N' h = 0 := by
    simp only [hN', smul_apply, innerSL_apply_apply, hxh, smul_zero]
  have hinv : HasFDerivAt (fun y : F ↦ ‖y‖⁻¹) ((-(‖x‖ ^ 2)⁻¹) • N') x :=
    (hasDerivAt_inv hx').comp_hasFDerivAt x hN
  have hf := (hN.cos.smul_const P).add ((hN.sin.mul hinv).smul L.hasFDerivAt)
  refine ⟨_, hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_), ?_⟩
  · simp only [div_eq_mul_inv]
    rfl
  · simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, hNh, zero_smul, add_zero, zero_add,
      smul_eq_mul, mul_zero, div_eq_mul_inv, Pi.mul_apply]

/-- The differential of the round-sphere exponential map in a direction orthogonal to a nonzero
base vector, in ambient coordinates: `d(exp_p)_x(h) = (sin ‖x‖ / ‖x‖) h`. -/
theorem mvfderiv_coe_mfderiv_riemannianExp_sphere_of_inner_eq_zero (p : sphere (0 : E) 1)
    {x h : TangentSpace (𝓡 n) p} (hx : x ≠ 0) (hxh : ⟪x, h⟫_ℝ = 0) :
    mvfderiv (𝓡 n) ι (riemannianExp (𝓡 n) (sphere (0 : E) 1) p x)
        (mfderiv 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) (riemannianExp (𝓡 n) (sphere (0 : E) 1) p)
          x h) =
      (Real.sin ‖x‖ / ‖x‖) • mvfderiv (𝓡 n) ι p h := by
  obtain ⟨D, hD, hDh⟩ := hasFDerivAt_cos_norm_smul_add_sinc_smul_apply_of_inner_eq_zero
    (p : E) (mvfderiv (𝓡 n) ι p) hx hxh
  have hexp : MDifferentiableAt 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n)
      (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) x :=
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
    (contMDiffAt_riemannianExp
      (by rw [expDomain_eq_univ_of_compactSpace]; trivial)).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ι (riemannianExp (𝓡 n) (sphere (0 : E) 1) p x) :=
    (contMDiff_coe_sphere (m := 1) _).mdifferentiableAt one_ne_zero
  have hcomp := mfderiv_comp_apply x hι hexp h
  rw [show ι ∘ riemannianExp (𝓡 n) (sphere (0 : E) 1) p = fun v ↦ Real.cos ‖v‖ • (p : E) +
      (Real.sin ‖v‖ / ‖v‖) • mvfderiv (𝓡 n) ι p v from funext (coe_riemannianExp_sphere p),
    mfderiv_eq_fderiv, hD.fderiv] at hcomp
  rw [mvfderiv_apply_eq_mfderiv_apply, ← hDh]
  exact hcomp.symm

/-- The angular differential of the round-sphere exponential map has norm `|sin r| ‖w‖`: the
angular Jacobi field `t ↦ d(exp_p)_(t v)(t w)` along the great circle of a unit vector `v` has
norm `|sin t| ‖w‖`. -/
theorem norm_mfderiv_riemannianExp_sphere_smul (p : sphere (0 : E) 1)
    {v w : TangentSpace (𝓡 n) p} (hv : ‖v‖ = 1) (hvw : ⟪v, w⟫_ℝ = 0) (r : ℝ) :
    ‖mfderiv 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) (riemannianExp (𝓡 n) (sphere (0 : E) 1) p)
        (r • v) (r • w)‖ = |Real.sin r| * ‖w‖ := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [zero_smul, zero_smul, Real.sin_zero, abs_zero, zero_mul]
    exact (congrArg norm (map_zero _)).trans norm_zero
  have hx : r • v ≠ 0 := smul_ne_zero hr (norm_ne_zero_iff.mp (hv.trans_ne one_ne_zero))
  have hxh : ⟪r • v, r • w⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hvw, mul_zero, mul_zero]
  rw [norm_tangentSpace_sphere, mvfderiv_coe_mfderiv_riemannianExp_sphere_of_inner_eq_zero p hx hxh,
    map_smul, smul_smul, norm_smul, ← norm_tangentSpace_sphere, norm_smul r v, hv, mul_one]
  simp only [Real.norm_eq_abs]
  congr 1
  rcases hr.lt_or_gt with h | h
  · rw [abs_of_neg h, Real.sin_neg, neg_div_neg_eq, div_mul_cancel₀ _ hr]
  · rw [abs_of_pos h, div_mul_cancel₀ _ hr]

/-- The polar Jacobian of the unit sphere: for a unit vector `v` and `w ⊥ v`,
`j(r) = ‖d(exp_p)_(r v)(r w)‖ = |sin r| ‖w‖`. -/
theorem polarJacobian_sphere (p : sphere (0 : E) 1) {v w : TangentSpace (𝓡 n) p} (hv : ‖v‖ = 1)
    (hvw : ⟪v, w⟫_ℝ = 0) (r : ℝ) : polarJacobian p v w r = |Real.sin r| * ‖w‖ := by
  rw [polarJacobian_eq_norm, norm_mfderiv_riemannianExp_sphere_smul p hv hvw r]

end TauCeti
