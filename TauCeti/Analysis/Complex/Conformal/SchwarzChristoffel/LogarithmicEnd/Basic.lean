/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Asymptotic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Logarithmic Schwarz--Christoffel ends at finite prevertices

A real prevertex with total exponent `-1` represents an end at infinity, not a finite
polygon vertex. If `C` is its nonzero prevertex coefficient, the normalized primitive has
local form `C * log (z - p) + H z`, with `H` holomorphic across `p`. In particular the
primitive escapes to infinity along every approach to `p` through the upper half-plane,
including tangential approaches.

These local ends allow Schwarz--Christoffel data to describe polygons with several vertices
at infinity. The results impose no integrability conditions at the other prevertices, and
coincident prevertices are handled by summing their exponents. They do not assert global
univalence or identify the image domain.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- At a real prevertex with total exponent `-1`, subtracting the prevertex coefficient times
`log (z - p)` from the Schwarz--Christoffel primitive gives a holomorphic function across
that prevertex. The equality holds on an entire upper half-disc, not just along a ray. -/
theorem exists_analyticOnNhd_eq_schwarzChristoffelPrimitive_sub_log_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    ∃ (H : ℂ → ℂ) (r : ℝ), 0 < r ∧ AnalyticOnNhd ℂ H (ball (p : ℂ) r) ∧
      ∀ z ∈ ball (p : ℂ) r ∩ upperHalfPlaneSet,
        schwarzChristoffelPrimitive a e z₀ z -
          schwarzChristoffelPrevertexCoefficient a e p * log (z - (p : ℂ)) = H z := by
  obtain ⟨g, hg, hgp, hfactor⟩ :=
    exists_analyticAt_schwarzChristoffelIntegrand_eq_cpow_mul a e p
  obtain ⟨r, hr, hgr⟩ := Metric.eventually_nhds_iff.mp
    (hg.eventually_analyticAt.mono fun _ h => h.differentiableAt)
  have hgd : DifferentiableOn ℂ g (ball (p : ℂ) r) := fun z hz =>
    (hgr hz).differentiableWithinAt
  -- The divided difference removes the simple pole from the derivative.
  have hds : DifferentiableOn ℂ (dslope g (p : ℂ)) (ball (p : ℂ) r) :=
    (differentiableOn_dslope (ball_mem_nhds _ hr)).mpr hgd
  have hderiv (z : ℂ) (hz : z ∈ ball (p : ℂ) r ∩ upperHalfPlaneSet) :
      HasDerivAt (fun z => schwarzChristoffelPrimitive a e z₀ z -
        schwarzChristoffelPrevertexCoefficient a e p * log (z - (p : ℂ)))
        (dslope g (p : ℂ) z) z := by
    have hzp : z ≠ (p : ℂ) := by
      intro h
      simp [h] at hz
    have hlog := (hasDerivAt_log (sub_ofReal_mem_slitPlane_of_im_pos hz.2 p)).comp z
      ((hasDerivAt_id z).sub_const (p : ℂ))
    have h := (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz.2).sub
      (hlog.const_mul (schwarzChristoffelPrevertexCoefficient a e p))
    apply h.congr_deriv
    rw [hfactor z hz.2, he]
    simp only [ofReal_neg, ofReal_one, cpow_neg_one, dslope_of_ne _ hzp,
      slope_def_field, hgp, mul_one]
    ring
  obtain ⟨H, hH, heq⟩ := exists_hasDerivAt_eqOn_ball_inter_upperHalfPlane hds hderiv
  have hHd : DifferentiableOn ℂ H (ball (p : ℂ) r) := fun z hz =>
    (hH z hz).differentiableAt.differentiableWithinAt
  exact ⟨H, r, hr, hHd.analyticOnNhd isOpen_ball, fun z hz => (heq hz).symm⟩

/-- After dividing by its nonzero prevertex coefficient, a logarithmic Schwarz--Christoffel
end has real part tending to negative infinity, uniformly over upper-half-plane approaches. -/
theorem tendsto_re_schwarzChristoffelPrimitive_div_coefficient_atBot_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    Tendsto (fun z => (schwarzChristoffelPrimitive a e z₀ z /
      schwarzChristoffelPrevertexCoefficient a e p).re)
      (𝓝[upperHalfPlaneSet] (p : ℂ)) atBot := by
  obtain ⟨H, r, hr, hH, heq⟩ :=
    exists_analyticOnNhd_eq_schwarzChristoffelPrimitive_sub_log_of_sum_eq_neg_one a e z₀ p he
  have hC := schwarzChristoffelPrevertexCoefficient_ne_zero a e p
  have hnorm : Tendsto (fun z : ℂ => ‖z - (p : ℂ)‖)
      (𝓝[upperHalfPlaneSet] (p : ℂ)) (𝓝[>] 0) := by
    exact (tendsto_norm_sub_self_nhdsNE (p : ℂ)).mono_left
      (nhdsWithin_mono _ fun z hz => by
        intro h
        simp [mem_singleton_iff.mp h] at hz)
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hnorm
  have hrem := (continuous_re.tendsto _ |>.comp
    ((hH _ (mem_ball_self hr)).continuousAt.div_const
      (schwarzChristoffelPrevertexCoefficient a e p)).tendsto).mono_left
    (nhdsWithin_le_nhds : 𝓝[upperHalfPlaneSet] (p : ℂ) ≤ 𝓝 (p : ℂ))
  refine (hlog.atBot_add hrem).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (p : ℂ) hr)] with z hz hzr
  have h := heq z ⟨hzr, hz⟩
  have hF : schwarzChristoffelPrimitive a e z₀ z /
      schwarzChristoffelPrevertexCoefficient a e p =
        log (z - (p : ℂ)) + H z / schwarzChristoffelPrevertexCoefficient a e p := by
    rw [← h]
    field_simp
    ring
  simp only [hF, add_re, log_re, Function.comp_apply]

/-- **Escape at a logarithmic prevertex.** If the total exponent at a real point is `-1`,
the Schwarz--Christoffel primitive tends to infinity there through the whole upper half-plane.
No assumptions on the other exponents or on global injectivity are needed. -/
theorem tendsto_schwarzChristoffelPrimitive_cobounded_of_prevertex_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    Tendsto (schwarzChristoffelPrimitive a e z₀)
      (𝓝[upperHalfPlaneSet] (p : ℂ)) (cobounded ℂ) := by
  have h := tendsto_re_schwarzChristoffelPrimitive_div_coefficient_atBot_of_sum_eq_neg_one
    a e z₀ p he
  have hnorm : Tendsto (fun z => ‖schwarzChristoffelPrimitive a e z₀ z /
      schwarzChristoffelPrevertexCoefficient a e p‖)
      (𝓝[upperHalfPlaneSet] (p : ℂ)) atTop :=
    tendsto_atTop_mono (fun z => (neg_le_abs _).trans (abs_re_le_norm _))
      (tendsto_neg_atBot_atTop.comp h)
  apply tendsto_norm_atTop_iff_cobounded.mp
  have hC : 0 < ‖schwarzChristoffelPrevertexCoefficient a e p‖ :=
    norm_pos_iff.mpr (schwarzChristoffelPrevertexCoefficient_ne_zero a e p)
  simpa only [norm_div, div_mul_cancel₀ _ hC.ne'] using hnorm.atTop_mul_const hC

end TauCeti
