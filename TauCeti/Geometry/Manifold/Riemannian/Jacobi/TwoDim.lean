/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Convexity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The scalar Jacobi equation on surfaces

Let `J` be a Jacobi field along a unit-speed geodesic `γ` of a two-dimensional Riemannian
manifold, and suppose that `J` is normal: `J` and its covariant derivative `DJ` are orthogonal to
`γ'`. Away from the zeros of `J`, its norm `j = ‖J‖` satisfies the scalar Jacobi equation
`j'' + K j = 0`, where `K` is the Gaussian curvature at the point of `γ`.

Indeed `j' = ⟨DJ, J⟩ / ‖J‖` and `(⟨DJ, J⟩)' = ‖DJ‖² - ⟨R(J, γ')γ', J⟩`. In dimension two, `J`
and `DJ` both lie in the line orthogonal to `γ'`, so `‖DJ‖² ‖J‖² = ⟨DJ, J⟩²` and the quotient
rule leaves `j'' = -⟨R(J, γ')γ', J⟩ / ‖J‖ = -K j`.

A Jacobi field is normal on a preconnected parameter set as soon as its initial data are
orthogonal to the velocity, so in the version with derivatives within the parameter set,
normality is only imposed at one parameter. The Gaussian curvature is the sectional curvature
of the tangent plane, or equivalently half the scalar curvature.

## Main results

* `TauCeti.Manifold.IsJacobiFieldOn.derivWithin_derivWithin_norm_add_sectionalCurvature_mul`:
  `j'' + K j = 0` with derivatives within a preconnected parameter set on which `J` does not
  vanish.
* `TauCeti.Manifold.IsJacobiFieldOn.deriv_deriv_norm_add_sectionalCurvature_mul`: `j'' + K j = 0`
  on an open parameter set, at every parameter where `J` does not vanish.
* `TauCeti.Manifold.IsJacobiFieldOn.deriv_deriv_norm_add_scalarCurvature_div_two_mul`: the same
  equation with `K` written as half the scalar curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (Jacobi fields).
* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, Prentice-Hall, 1976, §4-6
  (the equation `(√G)_ρρ + K √G = 0` in geodesic polar coordinates).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}

/-- In dimension two, the derivative `⟨DJ, J⟩ / ‖J‖` of the norm of a Jacobi field `J` is itself
differentiable, with derivative `-K ‖J‖`, at a unit-speed parameter where `J` is nonzero and both
`J` and `DJ` are orthogonal to `γ'`. Here `K` is the sectional curvature of the tangent plane. -/
theorem IsJacobiFieldOn.hasDerivWithinAt_inner_alongCurveWithin_self_div_norm_of_finrank_eq_two
    (h : IsJacobiFieldOn I γ V s) (ht : t ∈ s) (hV : V t ≠ 0)
    (hdim : Module.finrank ℝ (TangentSpace I (γ t)) = 2)
    (hunit : ‖curveVelocityWithin I γ s t‖ = 1)
    (hnormal : ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0)
    (hDnormal : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t,
      curveVelocityWithin I γ s t⟫_ℝ = 0) :
    HasDerivWithinAt
      (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s r, V r⟫_ℝ / ‖V r‖)
      (-(leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) (γ t) (V t)
          (curveVelocityWithin I γ s t) * ‖V t‖) s t := by
  have : Fact (Module.finrank ℝ (TangentSpace I (γ t)) = 2) := ⟨hdim⟩
  have hspeed : curveVelocityWithin I γ s t ≠ 0 := by
    intro hz
    simp [hz] at hunit
  have hcs : ‖alongCurveWithin (leviCivitaConnection I M) γ V s t‖ ^ 2 * ‖V t‖ ^ 2 =
      ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t, V t⟫_ℝ ^ 2 := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero hspeed hV
        (by rwa [real_inner_comm]) (by rwa [real_inner_comm]))
    rw [← hc, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    ring
  have hd := (h.hasDerivWithinAt_inner_alongCurveWithin_self ht).div
    (h.hasDerivWithinAt_norm ht hV) (norm_ne_zero_iff.mpr hV)
  apply hd.congr_deriv
  rw [sectionalCurvature_apply, Matrix.real_det_gram_fin_two, hnormal,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hunit]
  simp only [one_pow, mul_one, zero_pow two_ne_zero, sub_zero]
  field_simp [norm_ne_zero_iff.mpr hV]
  nlinarith [hcs]

/-- **The scalar Jacobi equation on a surface**, with derivatives within the parameter set. Let
`J` be a Jacobi field along a geodesic `γ` on a preconnected parameter set on which `J` does not
vanish, with `J` and `DJ` orthogonal to `γ'` at one parameter `a`. At a unit-speed parameter `t`
where the tangent space has dimension two, `j = ‖J‖` satisfies `j'' + K j = 0`. -/
theorem IsJacobiFieldOn.derivWithin_derivWithin_norm_add_sectionalCurvature_mul
    (h : IsJacobiFieldOn I γ V s) (hs : IsPreconnected s) {a : ℝ} (ha : a ∈ s)
    (hV : ∀ r ∈ s, V r ≠ 0)
    (hnormal : ⟪V a, curveVelocityWithin I γ s a⟫_ℝ = 0)
    (hDnormal : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s a,
      curveVelocityWithin I γ s a⟫_ℝ = 0)
    (ht : t ∈ s) (hdim : Module.finrank ℝ (TangentSpace I (γ t)) = 2)
    (hunit : ‖curveVelocityWithin I γ s t‖ = 1) :
    derivWithin (derivWithin (fun r ↦ ‖V r‖) s) s t +
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) (γ t) (V t)
          (curveVelocityWithin I γ s t) * ‖V t‖ = 0 := by
  have hn := (h.forall_inner_curveVelocityWithin_eq_zero_iff hs ha).2 ⟨hnormal, hDnormal⟩
  have hdn : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t,
      curveVelocityWithin I γ s t⟫_ℝ = 0 := by
    rw [← h.inner_alongCurveWithin_curveVelocityWithin_eq hs ha ht, hDnormal]
  have hd := (h.hasDerivWithinAt_inner_alongCurveWithin_self_div_norm_of_finrank_eq_two ht
    (hV t ht) hdim hunit (hn t ht) hdn).congr_of_mem (fun r hr ↦
      (h.hasDerivWithinAt_norm hr (hV r hr)).derivWithin (h.uniqueDiffOn r hr)) ht
  rw [hd.derivWithin (h.uniqueDiffOn t ht)]
  ring

/-- **The scalar Jacobi equation on a surface.** Let `J` be a Jacobi field along a geodesic `γ`
on an open parameter set. At a unit-speed parameter `t` where the tangent space has dimension two
and `J` is nonzero and normal, with `DJ` also orthogonal to `γ'`, `j = ‖J‖` satisfies
`j'' + K j = 0`, even if `J` vanishes elsewhere along `γ`. -/
theorem IsJacobiFieldOn.deriv_deriv_norm_add_sectionalCurvature_mul (h : IsJacobiFieldOn I γ V s)
    (hs : IsOpen s) (ht : t ∈ s) (hV : V t ≠ 0)
    (hdim : Module.finrank ℝ (TangentSpace I (γ t)) = 2)
    (hunit : ‖curveVelocityWithin I γ s t‖ = 1)
    (hnormal : ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0)
    (hDnormal : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t,
      curveVelocityWithin I γ s t⟫_ℝ = 0) :
    deriv (deriv (fun r ↦ ‖V r‖)) t +
      (leviCivitaConnection I M).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection I) (γ t) (V t)
          (curveVelocityWithin I γ s t) * ‖V t‖ = 0 := by
  have hd0 := (h.hasDerivWithinAt_norm ht hV).hasDerivAt (hs.mem_nhds ht)
  have hne : ∀ᶠ r in 𝓝 t, ‖V r‖ ≠ 0 := hd0.continuousAt.eventually_ne
    (norm_ne_zero_iff.mpr hV)
  have heq : deriv (fun r ↦ ‖V r‖) =ᶠ[𝓝 t]
      (fun r ↦ ⟪alongCurveWithin (leviCivitaConnection I M) γ V s r, V r⟫_ℝ / ‖V r‖) := by
    filter_upwards [hs.mem_nhds ht, hne] with r hr hnr
    exact ((h.hasDerivWithinAt_norm hr (norm_ne_zero_iff.mp hnr)).hasDerivAt
      (hs.mem_nhds hr)).deriv
  have hd := ((h.hasDerivWithinAt_inner_alongCurveWithin_self_div_norm_of_finrank_eq_two ht hV
    hdim hunit hnormal hDnormal).hasDerivAt (hs.mem_nhds ht)).congr_of_eventuallyEq heq
  rw [hd.deriv]
  ring

/-- **The scalar Jacobi equation on a surface**, with the Gaussian curvature written as half the
scalar curvature at the point of the geodesic. -/
theorem IsJacobiFieldOn.deriv_deriv_norm_add_scalarCurvature_div_two_mul
    (h : IsJacobiFieldOn I γ V s) (hs : IsOpen s) (ht : t ∈ s) (hV : V t ≠ 0)
    (hdim : Module.finrank ℝ (TangentSpace I (γ t)) = 2)
    (hunit : ‖curveVelocityWithin I γ s t‖ = 1)
    (hnormal : ⟪V t, curveVelocityWithin I γ s t⟫_ℝ = 0)
    (hDnormal : ⟪alongCurveWithin (leviCivitaConnection I M) γ V s t,
      curveVelocityWithin I γ s t⟫_ℝ = 0) :
    deriv (deriv (fun r ↦ ‖V r‖)) t +
      ((leviCivitaConnection I M).scalarCurvature (γ t) / 2) * ‖V t‖ = 0 := by
  have hli : LinearIndependent ℝ ![V t, curveVelocityWithin I γ s t] := by
    apply Matrix.det_gram_ne_zero_iff_linearIndependent.mp
    rw [Matrix.real_det_gram_fin_two, hnormal, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hunit]
    simpa only [one_pow, mul_one, zero_pow two_ne_zero, sub_zero] using
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hV)
  have hK := ((leviCivitaConnection I M).hasSectionalCurvatureAt_scalarCurvature_div_two
    (isMetricCompatible_leviCivitaConnection I) hdim).sectionalCurvature_eq _ _ hli
  simpa only [hK] using h.deriv_deriv_norm_add_sectionalCurvature_mul hs ht hV hdim hunit hnormal
    hDnormal

end TauCeti.Manifold
