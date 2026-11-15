/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar.Jacobian
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.TwoDim
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Basic
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential

/-!
# The scalar Jacobi equation for the polar Jacobian

Let `p` be a point of a two-dimensional Riemannian manifold, `v` a unit tangent vector at `p` and
`w` a tangent vector at `p` orthogonal to `v`. The angular differential
`r ↦ d(exp_p)_(r v)(r w)` is a Jacobi field along the radial geodesic `r ↦ exp_p (r v)`, normal to
it. Its norm is the polar Jacobian `j(r) = polarJacobian p v w r`, so wherever `j(r) ≠ 0` it
satisfies the scalar Jacobi equation

`j''(r) + K(exp_p (r v)) j(r) = 0`,

where `K` is the Gaussian curvature. No curvature hypothesis is made. In geodesic polar
coordinates `F(r, θ) = exp_p (r e(θ))`, with `e(θ)` the unit circle in angular arclength and
`w = e′(θ)`, this is the equation `j_rr + (K ∘ F) j = 0` for the coefficient `j` of
`F*g = dr² + j² dθ²`. Inside a normal domain, `j(r) ≠ 0` for `r ≠ 0` and `w ≠ 0`
(`TauCeti.Manifold.IsNormalDomain.polarJacobian_pos`).

## Main results

* `TauCeti.Manifold.deriv_deriv_polarJacobian_add_sectionalCurvature_mul`: `j'' + K j = 0`, with
  `K` the sectional curvature of the plane spanned by the angular and radial velocities.
* `TauCeti.Manifold.deriv_deriv_polarJacobian_add_scalarCurvature_div_two_mul`: the same equation
  with `K` written as half the scalar curvature, a function of the point alone.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (Jacobi fields and the differential of the exponential map).
* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Prentice-Hall, 1976, §4-6
  (the equation `(√G)_ρρ + K √G = 0` in geodesic polar coordinates).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v w : TangentSpace I p} {r : ℝ}

/-- The velocity of the radial geodesic `t ↦ exp_p (t v)` at `r` is `d(exp_p)_(r v) v`, it has
unit length when `v` does, and the angular Jacobi field `d(exp_p)_(t v)(t w)` and its covariant
derivative are orthogonal to it at `r` when `w` is orthogonal to `v`. -/
private theorem polarJacobian_jacobi_data (hmem : r • v ∈ expDomain I M p) (hv : ‖v‖ = 1)
    (hvw : ⟪v, w⟫_ℝ = 0) :
    curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v))
        (geodesicInterval I M p v) r =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) v ∧
    ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) v‖ = 1 ∧
    ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) (r • w),
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) v⟫_ℝ = 0 ∧
    ⟪alongCurveWithin (leviCivitaConnection I M) (fun t : ℝ ↦ riemannianExp I M p (t • v))
        (fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w))
        (geodesicInterval I M p v) r,
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) v⟫_ℝ = 0 := by
  have ht := mem_geodesicInterval_iff_smul_mem_expDomain.mpr hmem
  have hvel : curveVelocityWithin I (fun t : ℝ ↦ riemannianExp I M p (t • v))
      (geodesicInterval I M p v) r =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) v := by
    rw [curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds ht),
      curveVelocity_riemannianExp_smul hmem]
  refine ⟨hvel, ?_, ?_, ?_⟩
  · have hg := inner_mfderiv_riemannianExp_unit_radial hmem hv
    rw [real_inner_self_eq_norm_sq] at hg
    nlinarith [norm_nonneg (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) v)]
  · rw [real_inner_comm]
    exact inner_mfderiv_riemannianExp_radial_angular hmem hvw
  · have hJ := isJacobiFieldOn_mfderiv_riemannianExp (I := I) p v w
    rw [← hvel, ← hJ.inner_alongCurveWithin_curveVelocityWithin_eq
      isPreconnected_geodesicInterval zero_mem_geodesicInterval ht,
      alongCurveWithin_mfderiv_riemannianExp_zero,
      curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval),
      curveVelocity_riemannianExp_smul_zero, zero_smul, riemannianExp_zero]
    exact (real_inner_comm v w).trans hvw

/-- **The scalar Jacobi equation for the polar Jacobian.** Let `v` be a unit tangent vector at
`p` and `w` a tangent vector orthogonal to it, in dimension two. If `r • v` lies in the domain of
`exp_p` and the polar Jacobian `j = polarJacobian p v w` does not vanish at `r`, then
`j''(r) + K j(r) = 0`, where `K` is the sectional curvature at `exp_p (r v)` of the plane spanned
by `d(exp_p)_(r v)(r w)` and `d(exp_p)_(r v) v`. -/
theorem deriv_deriv_polarJacobian_add_sectionalCurvature_mul (hmem : r • v ∈ expDomain I M p)
    (hj : polarJacobian (I := I) p v w r ≠ 0) (hv : ‖v‖ = 1) (hvw : ⟪v, w⟫_ℝ = 0)
    (hdim : Module.finrank ℝ (TangentSpace I (riemannianExp I M p (r • v))) = 2) :
    deriv (deriv (polarJacobian (I := I) p v w)) r +
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (r • v))
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) (r • w))
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) v) *
          polarJacobian (I := I) p v w r = 0 := by
  obtain ⟨hvel, hunit, hn, hdn⟩ := polarJacobian_jacobi_data hmem hv hvw
  rw [polarJacobian_eq_norm, Ne, norm_eq_zero] at hj
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp (I := I) p v w
  have hODE := hJ.deriv_deriv_norm_add_sectionalCurvature_mul isOpen_geodesicInterval
    (mem_geodesicInterval_iff_smul_mem_expDomain.mpr hmem) hj hdim
    (hvel ▸ hunit) (hvel ▸ hn) (hvel ▸ hdn)
  simpa only [hvel, ← polarJacobian_eq_norm] using hODE

/-- **The scalar Jacobi equation for the polar Jacobian**, with the Gaussian curvature written as
half the scalar curvature at `exp_p (r v)`. Under the hypotheses of
`TauCeti.Manifold.deriv_deriv_polarJacobian_add_sectionalCurvature_mul`,
`j''(r) + (Scal(exp_p (r v)) / 2) j(r) = 0`. -/
theorem deriv_deriv_polarJacobian_add_scalarCurvature_div_two_mul
    (hmem : r • v ∈ expDomain I M p) (hj : polarJacobian (I := I) p v w r ≠ 0) (hv : ‖v‖ = 1)
    (hvw : ⟪v, w⟫_ℝ = 0)
    (hdim : Module.finrank ℝ (TangentSpace I (riemannianExp I M p (r • v))) = 2) :
    deriv (deriv (polarJacobian (I := I) p v w)) r +
      ((leviCivitaConnection I M).scalarCurvature (riemannianExp I M p (r • v)) / 2) *
        polarJacobian (I := I) p v w r = 0 := by
  obtain ⟨hvel, hunit, hn, hdn⟩ := polarJacobian_jacobi_data hmem hv hvw
  rw [polarJacobian_eq_norm, Ne, norm_eq_zero] at hj
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp (I := I) p v w
  have hODE := hJ.deriv_deriv_norm_add_scalarCurvature_div_two_mul isOpen_geodesicInterval
    (mem_geodesicInterval_iff_smul_mem_expDomain.mpr hmem) hj hdim
    (hvel ▸ hunit) (hvel ▸ hn) (hvel ▸ hdn)
  simpa only [← polarJacobian_eq_norm] using hODE

end TauCeti.Manifold
