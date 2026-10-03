/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Asymptotic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Logarithmic growth of Schwarz--Christoffel primitives

When the total turning exponent is `-1`, the Schwarz--Christoffel primitive grows
logarithmically. Subtracting the principal logarithm leaves a function holomorphic in the
reciprocal coordinate at zero for points in the upper half-plane. Consequently the difference
has a finite limit at infinity,
with first correction `(∑ i, e i * a i) / z`, and the primitive escapes every bounded set.
All limits hold through the whole upper half-plane, including tangential approaches to its
real boundary. This is the logarithmic endpoint of the growth estimates used to establish
properness of maps onto unbounded polygonal domains.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- If the total exponent is `-1`, subtracting the principal logarithm from the
Schwarz--Christoffel primitive gives a holomorphic function of `-1 / z` near infinity
in the upper half-plane.
Its reciprocal-coordinate derivative at zero is the negative weighted sum of prevertices. -/
private theorem
    exists_differentiableOn_eq_schwarzChristoffelPrimitive_sub_log_comp_neg_inv_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    ∃ (H : ℂ → ℂ) (r : ℝ), 0 < r ∧ DifferentiableOn ℂ H (ball 0 r) ∧
      HasDerivAt H (-∑ i, (e i : ℂ) * (a i : ℂ)) 0 ∧
      ∀ z ∈ upperHalfPlaneSet, ‖z⁻¹‖ < r →
        schwarzChristoffelPrimitive a e z₀ z - log z = H (-z⁻¹) := by
  classical
  let q : ℂ → ℂ := fun w => ∏ i, (1 + (a i : ℂ) * w) ^ (e i : ℂ)
  have hq0 : q 0 = 1 := by simp [q]
  -- In the reciprocal coordinate the normalized integrand is holomorphic at zero.
  have hq : AnalyticAt ℂ q 0 := by
    simpa [q] using analyticAt_prod_one_sub_mul_cpow
      (fun i => -(a i : ℂ)) (fun i => (e i : ℂ))
  obtain ⟨r, hr, hqr⟩ := Metric.eventually_nhds_iff.mp
    (hq.eventually_analyticAt.mono fun _ h => h.differentiableAt)
  have hqd : DifferentiableOn ℂ q (ball 0 r) := fun w hw =>
    (hqr (by simpa [dist_zero_right] using hw)).differentiableWithinAt
  have hds : DifferentiableOn ℂ (fun w => -dslope q 0 w) (ball 0 r) :=
    ((differentiableOn_dslope (ball_mem_nhds 0 hr)).mpr hqd).neg
  -- Match the primitive to the logarithmic remainder on the connected half-disc.
  have hderiv (w : ℂ) (hw : w ∈ ball (0 : ℂ) r ∩ upperHalfPlaneSet) : HasDerivAt
      (fun w => schwarzChristoffelPrimitive a e z₀ (-w⁻¹) - log (-w⁻¹))
      (-dslope q 0 w) w := by
    have hw0 : w ≠ 0 := fun h => by simpa [h] using hw.2
    have hwinv : -w⁻¹ ∈ upperHalfPlaneSet := im_neg_inv_pos.mpr hw.2
    have hinv := (hasDerivAt_inv hw0).neg
    have hf := (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hwinv).comp w hinv
    have hl := (hasDerivAt_log (mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hwinv)))).comp w hinv
    have heq : schwarzChristoffelIntegrand a e (-w⁻¹) = -w * q w := by
      have h := schwarzChristoffelIntegrand_div_cpow_eq_prod a e hwinv
      simp only [hsum, ofReal_neg, ofReal_one, cpow_neg_one, inv_neg, inv_inv,
        mul_neg, sub_neg_eq_add] at h
      simpa [q, mul_comm] using (div_eq_iff (neg_ne_zero.mpr hw0)).mp h
    convert hf.fun_sub hl using 1
    · rfl -- Unfold the compositions from `HasDerivAt.comp`.
    · rw [heq, dslope_of_ne q hw0]
      simp only [slope, hq0, sub_zero, smul_eq_mul, inv_neg, inv_inv, vsub_eq_sub]
      field_simp
      ring
  obtain ⟨H, hH, heq⟩ := exists_hasDerivAt_eqOn_ball_inter_upperHalfPlane hds hderiv
  -- The derivative at zero records the first correction to the logarithmic leading term.
  have hq' : HasDerivAt q (∑ i, (e i : ℂ) * (a i : ℂ)) 0 := by
    simpa [q] using hasDerivAt_prod_one_sub_mul_cpow
      (fun i => -(a i : ℂ)) (fun i => (e i : ℂ))
  refine ⟨H, r, hr,
    (fun w hw => (hH w hw).differentiableAt.differentiableWithinAt), ?_, ?_⟩
  · simpa [dslope_same, hq'.deriv] using hH 0 (mem_ball_self hr)
  · intro z hz hzr
    simpa using (heq ⟨by simpa [mem_ball_zero_iff] using hzr, im_neg_inv_pos.mpr hz⟩).symm

/-- **Logarithmic asymptotic at infinity.** If the total turning exponent is `-1`, there
is a constant `c` such that `F(z) = log z + c + (∑ i, e i * a i) / z + o(1 / z)`.
Both limits hold throughout the upper half-plane, without restrictions on its approach
directions or on the individual prevertices and exponents. -/
private theorem
    exists_tendsto_schwarzChristoffelPrimitive_sub_log_and_tendsto_mul_sub_atInfinity
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    ∃ c : ℂ,
      Tendsto (fun z => schwarzChristoffelPrimitive a e z₀ z - log z)
        (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 c) ∧
      Tendsto (fun z => z * (schwarzChristoffelPrimitive a e z₀ z - log z - c))
        (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (∑ i, (e i : ℂ) * (a i : ℂ))) := by
  obtain ⟨H, r, hr, _, hH, heq⟩ :=
    exists_differentiableOn_eq_schwarzChristoffelPrimitive_sub_log_comp_neg_inv_of_sum_eq_neg_one
      a e z₀ hsum
  have hinv : Tendsto (fun z : ℂ => -z⁻¹)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 0) := by
    simpa using (tendsto_inv₀_cobounded (α := ℂ)).neg.mono_left
      (inf_le_left : cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet ≤ cobounded ℂ)
  have hinv' : Tendsto (fun z : ℂ => -z⁻¹)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hinv, ?_⟩
    filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
    simpa using (inv_ne_zero (fun h => by simp [h] at hz))
  have hevent : (fun z => schwarzChristoffelPrimitive a e z₀ z - log z)
      =ᶠ[cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet] (fun z => H (-z⁻¹)) := by
    filter_upwards [hinv.eventually (ball_mem_nhds 0 hr),
      mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hzr hz
    exact heq z hz (by simpa [mem_ball_zero_iff] using hzr)
  refine ⟨H 0, (hH.continuousAt.tendsto.comp hinv).congr' hevent.symm, ?_⟩
  have h := (hH.tendsto_slope_zero.comp hinv').neg
  simp only [Function.comp_apply, zero_add, smul_eq_mul, inv_neg, inv_inv,
    neg_mul, neg_neg] at h
  refine h.congr' ?_
  filter_upwards [hevent] with z hz
  rw [hz]

/-- The constant term after subtracting the principal logarithm from the
Schwarz--Christoffel primitive at infinity. It is a genuine limit through the upper half-plane
when the total turning exponent is `-1`. -/
def schwarzChristoffelLogConstantAtInfinity (a e : ι → ℝ) (z₀ : UpperHalfPlane) : ℂ :=
  limUnder (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
    (fun z => schwarzChristoffelPrimitive a e z₀ z - log z)

/-- The logarithmic remainder tends to its constant term through the entire upper half-plane. -/
theorem tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    Tendsto (fun z => schwarzChristoffelPrimitive a e z₀ z - log z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
      (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀)) := by
  obtain ⟨c, hc, _⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_sub_log_and_tendsto_mul_sub_atInfinity a e z₀ hsum
  rwa [schwarzChristoffelLogConstantAtInfinity, hc.limUnder_eq]

/-- The first correction to the logarithmic asymptotic is the weighted sum of prevertices,
uniformly over all directions in the upper half-plane. -/
theorem tendsto_mul_schwarzChristoffelPrimitive_sub_log_sub_logConstantAtInfinity
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    Tendsto (fun z => z * (schwarzChristoffelPrimitive a e z₀ z - log z -
      schwarzChristoffelLogConstantAtInfinity a e z₀))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (∑ i, (e i : ℂ) * (a i : ℂ))) := by
  obtain ⟨c, hc, hcorrection⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_sub_log_and_tendsto_mul_sub_atInfinity a e z₀ hsum
  rwa [schwarzChristoffelLogConstantAtInfinity, hc.limUnder_eq]

/-- Changing the base point translates the logarithmic constant by the same constant
as the primitive. -/
theorem schwarzChristoffelLogConstantAtInfinity_change_base
    (a e : ι → ℝ) (b c : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    schwarzChristoffelLogConstantAtInfinity a e b =
      schwarzChristoffelLogConstantAtInfinity a e c - schwarzChristoffelPrimitive a e c b := by
  refine tendsto_nhds_unique (tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e b hsum) ?_
  refine Tendsto.congr' ?_
    ((tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e c hsum).sub tendsto_const_nhds)
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
  rw [schwarzChristoffelPrimitive_change_base a e b c hz]
  ring

/-- In the logarithmic case the real part of the Schwarz--Christoffel primitive tends to
positive infinity through the entire upper half-plane. -/
theorem tendsto_re_schwarzChristoffelPrimitive_atTop_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    Tendsto (fun z => (schwarzChristoffelPrimitive a e z₀ z).re)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) atTop := by
  have hc := tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e z₀ hsum
  have hlog : Tendsto (fun z : ℂ => Real.log ‖z‖)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) atTop :=
    (Real.tendsto_log_atTop.comp (tendsto_norm_atTop_iff_cobounded.mpr tendsto_id)).mono_left
      inf_le_left
  have h := hlog.atTop_add
    (continuous_re.tendsto (schwarzChristoffelLogConstantAtInfinity a e z₀) |>.comp hc)
  simpa [log_re] using h

/-- **Uniform escape in the logarithmic case.** A Schwarz--Christoffel primitive with total
turning exponent `-1` tends to infinity through the entire upper half-plane. -/
theorem tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    Tendsto (schwarzChristoffelPrimitive a e z₀)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  exact tendsto_atTop_mono (fun z => re_le_norm _)
    (tendsto_re_schwarzChristoffelPrimitive_atTop_of_sum_eq_neg_one a e z₀ hsum)

end TauCeti
