/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.EdgeIntersection
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Asymptotic
import TauCeti.Analysis.Complex.UpperHalfPlane.Primitive
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Quadratic growth of Schwarz--Christoffel primitives and ends of opening `2π`

Write `M = ∑ i, e i * a i` and `C = (M ^ 2 - ∑ i, e i * a i ^ 2) / 2`. When the total turning
exponent is `1`, the Schwarz--Christoffel primitive has the expansion

`F(z) = z ^ 2 / 2 - M * z + C * log z + c + o(1)`

as `z` tends to infinity through the whole upper half-plane, including tangential approaches
to the real axis. After subtracting these three terms, the primitive is holomorphic in the
reciprocal coordinate `-1 / z` at zero.

The same expansion holds for the canonical boundary values on the real axis beyond every
prevertex, with `log x` on the right and `log (-x) + π * I` on the left. Consequently the two
outer sides of the normalized boundary are horizontal rays pointing to the right, at the heights
`im c` and `im c + π * C`. They are disjoint exactly when `C ≠ 0`; when `C = 0` they overlap,
as for the slit plane `z ↦ z ^ 2`. Thus `π * C` is the signed distance between the supporting
lines of the two parallel outer sides of an end of opening `2π`, and `C ≠ 0` replaces the
outer-ray disjointness condition of the boundary-simplicity criterion.

When `C < 0`, far out in the upper half-plane, the comparison function
`z ^ 2 / 2 - M * z + C * log z` takes no value with real part greater than `1 / 2` in a band
strictly between the heights `π * C` and `0` that stays a fixed distance away from both.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- If the total exponent is one, subtracting the quadratic, linear and logarithmic terms from
the Schwarz--Christoffel primitive gives a holomorphic function of `-1 / z` near infinity in the
upper half-plane. -/
private theorem exists_differentiableOn_eq_schwarzChristoffelPrimitive_sub_comp_neg_inv
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = 1) :
    ∃ (H : ℂ → ℂ) (r : ℝ), 0 < r ∧ DifferentiableOn ℂ H (ball 0 r) ∧
      ∀ z ∈ upperHalfPlaneSet, ‖z⁻¹‖ < r →
        schwarzChristoffelPrimitive a e z₀ z - (z ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * z +
          ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 * log z) =
          H (-z⁻¹) := by
  classical
  set M : ℂ := ∑ i, (e i : ℂ) * (a i : ℂ)
  set C : ℂ := (M ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 with hC
  -- In the reciprocal coordinate `w = -1 / z`, the normalized integrand is the product `q`.
  set q : ℂ → ℂ := fun w => ∏ i, (1 - -(a i : ℂ) * w) ^ (e i : ℂ)
  have hq : AnalyticAt ℂ q 0 := analyticAt_prod_one_sub_mul_cpow _ _
  have hq0 : q 0 = 1 := by simp [q]
  have hq' : HasDerivAt q M 0 := by
    simpa [q, M, Finset.sum_neg_distrib] using
      hasDerivAt_prod_one_sub_mul_cpow (fun i => -(a i : ℂ)) (fun i => (e i : ℂ))
  obtain ⟨r, hr, hqr⟩ := Metric.eventually_nhds_iff.mp
    (hq.eventually_analyticAt.mono fun _ h => h.differentiableAt)
  have hball : ball (0 : ℂ) r ∈ 𝓝 0 := ball_mem_nhds 0 hr
  have hqd : DifferentiableOn ℂ q (ball 0 r) := fun w hw =>
    (hqr (by simpa [dist_zero_right] using hw)).differentiableWithinAt
  -- Three divided differences at zero remove the Taylor terms of order `0`, `1` and `2`.
  have hD₁ : DifferentiableOn ℂ (dslope q 0) (ball 0 r) := (differentiableOn_dslope hball).mpr hqd
  have hD₂ : DifferentiableOn ℂ (dslope (dslope q 0) 0) (ball 0 r) :=
    (differentiableOn_dslope hball).mpr hD₁
  have hD₃ : DifferentiableOn ℂ (dslope (dslope (dslope q 0) 0) 0) (ball 0 r) :=
    (differentiableOn_dslope hball).mpr hD₂
  have hD₁w (w : ℂ) (hw : w ≠ 0) : dslope q 0 w = (q w - 1) / w := by
    rw [dslope_of_ne _ hw, slope_def_field, hq0, sub_zero]
  have hD₂w (w : ℂ) (hw : w ≠ 0) : dslope (dslope q 0) 0 w = (dslope q 0 w - M) / w := by
    rw [dslope_of_ne _ hw, slope_def_field, dslope_same, hq'.deriv, sub_zero]
  -- The second divided difference at zero is the second-order coefficient `C`.
  have hD₂0 : dslope (dslope q 0) 0 0 = C := by
    have hcont : Tendsto (dslope (dslope q 0) 0) (𝓝[≠] 0)
        (𝓝 (dslope (dslope q 0) 0 0)) :=
      ((hD₂ 0 (mem_ball_self hr)).differentiableAt hball).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hneg : ∑ i, (e i : ℂ) * -(a i : ℂ) = -M := by simp [M, Finset.sum_neg_distrib]
    have hlim : Tendsto (fun w => (q w - 1 + (∑ i, (e i : ℂ) * -(a i : ℂ)) * w) / w ^ 2)
        (𝓝[≠] 0)
        (𝓝 (((∑ i, (e i : ℂ) * -(a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (-(a i : ℂ)) ^ 2) / 2)) :=
      tendsto_prod_one_sub_mul_cpow_sub_linear_div_sq (fun i => -(a i : ℂ)) (fun i => (e i : ℂ))
    simp only [hneg, neg_sq, ← hC] at hlim
    refine tendsto_nhds_unique hcont (hlim.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := hw
    rw [hD₂w w hw0, hD₁w w hw0]
    field_simp
    ring
  have hD₃w (w : ℂ) (hw : w ≠ 0) :
      dslope (dslope (dslope q 0) 0) 0 w = (dslope (dslope q 0) 0 w - C) / w := by
    rw [dslope_of_ne _ hw, slope_def_field, hD₂0, sub_zero]
  -- Match the remainder of the primitive with a primitive of `-dslope³ q` on the half-disc.
  have hderiv (w : ℂ) (hw : w ∈ ball (0 : ℂ) r ∩ upperHalfPlaneSet) : HasDerivAt
      (fun w => schwarzChristoffelPrimitive a e z₀ (-w⁻¹) -
        ((-w⁻¹) ^ 2 / 2 - M * (-w⁻¹) + C * log (-w⁻¹)))
      (-dslope (dslope (dslope q 0) 0) 0 w) w := by
    have hw0 : w ≠ 0 := fun h => by simpa [h] using hw.2
    have hwinv : -w⁻¹ ∈ upperHalfPlaneSet := im_neg_inv_pos.mpr hw.2
    have hslit : -w⁻¹ ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hwinv))
    have hinv := (hasDerivAt_inv hw0).neg
    have hf := (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hwinv).comp w hinv
    have hp := ((((hasDerivAt_pow 2 (-w⁻¹)).div_const 2).sub
      ((hasDerivAt_id (-w⁻¹)).const_mul M)).add ((hasDerivAt_log hslit).const_mul C)).comp w hinv
    have heq : schwarzChristoffelIntegrand a e (-w⁻¹) = -w⁻¹ * q w := by
      have h := schwarzChristoffelIntegrand_div_cpow_eq_prod a e hwinv
      simp only [hsum, ofReal_one, cpow_one, inv_neg, inv_inv] at h
      rw [div_eq_iff (neg_ne_zero.mpr (inv_ne_zero hw0))] at h
      rw [h, mul_comm]
      simp [q]
    convert hf.fun_sub hp using 1
    · rfl -- Unfold the compositions from `HasDerivAt.comp`.
    · rw [heq, hD₃w w hw0, hD₂w w hw0, hD₁w w hw0]
      norm_num
      field_simp
      ring
  obtain ⟨H, hH, heq⟩ := exists_hasDerivAt_eqOn_ball_inter_upperHalfPlane hD₃.neg hderiv
  refine ⟨H, r, hr, fun w hw => (hH w hw).differentiableAt.differentiableWithinAt, ?_⟩
  intro z hz hzr
  simpa using (heq ⟨by simpa [mem_ball_zero_iff] using hzr, im_neg_inv_pos.mpr hz⟩).symm

/-- The constant term of a Schwarz--Christoffel primitive at infinity after subtracting its
quadratic, linear and logarithmic terms. It is a genuine limit through the upper half-plane when
the total turning exponent is `1`. -/
def schwarzChristoffelQuadraticConstantAtInfinity (a e : ι → ℝ) (z₀ : UpperHalfPlane) : ℂ :=
  limUnder (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
    (fun z => schwarzChristoffelPrimitive a e z₀ z -
      (z ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * z +
        ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 * log z))

/-- The witness of the reciprocal-coordinate expansion takes the value of the constant term
at zero. -/
private theorem exists_differentiableOn_eq_comp_neg_inv_and_eq_quadraticConstantAtInfinity
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = 1) :
    ∃ (H : ℂ → ℂ) (r : ℝ), 0 < r ∧ DifferentiableOn ℂ H (ball 0 r) ∧
      H 0 = schwarzChristoffelQuadraticConstantAtInfinity a e z₀ ∧
      ∀ z ∈ upperHalfPlaneSet, ‖z⁻¹‖ < r →
        schwarzChristoffelPrimitive a e z₀ z - (z ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * z +
          ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 * log z) =
          H (-z⁻¹) := by
  obtain ⟨H, r, hr, hH, heq⟩ :=
    exists_differentiableOn_eq_schwarzChristoffelPrimitive_sub_comp_neg_inv a e z₀ hsum
  refine ⟨H, r, hr, hH, ?_, heq⟩
  have hinv : Tendsto (fun z : ℂ => -z⁻¹)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 0) := by
    simpa using (tendsto_inv₀_cobounded (α := ℂ)).neg.mono_left
      (inf_le_left : cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet ≤ cobounded ℂ)
  have hlim := ((hH 0 (mem_ball_self hr)).differentiableAt
    (ball_mem_nhds 0 hr)).continuousAt.tendsto.comp hinv
  refine (Tendsto.limUnder_eq (hlim.congr' ?_)).symm
  filter_upwards [hinv.eventually (ball_mem_nhds 0 hr),
    mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hzr hz
  exact (heq z hz (by simpa [mem_ball_zero_iff] using hzr)).symm

/-- **Quadratic asymptotic at infinity.** If the total turning exponent is `1`, then
`F(z) - (z ^ 2 / 2 - M * z + C * log z)` has a finite limit through the entire upper
half-plane, where `M = ∑ i, e i * a i` and `C = (M ^ 2 - ∑ i, e i * a i ^ 2) / 2`. -/
theorem tendsto_schwarzChristoffelPrimitive_sub_quadratic_atInfinity_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = 1) :
    Tendsto (fun z => schwarzChristoffelPrimitive a e z₀ z -
      (z ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * z +
        ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 * log z))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
      (𝓝 (schwarzChristoffelQuadraticConstantAtInfinity a e z₀)) := by
  obtain ⟨H, r, hr, hH, hH0, heq⟩ :=
    exists_differentiableOn_eq_comp_neg_inv_and_eq_quadraticConstantAtInfinity a e z₀ hsum
  have hinv : Tendsto (fun z : ℂ => -z⁻¹)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 0) := by
    simpa using (tendsto_inv₀_cobounded (α := ℂ)).neg.mono_left
      (inf_le_left : cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet ≤ cobounded ℂ)
  rw [← hH0]
  refine (((hH 0 (mem_ball_self hr)).differentiableAt
    (ball_mem_nhds 0 hr)).continuousAt.tendsto.comp hinv).congr' ?_
  filter_upwards [hinv.eventually (ball_mem_nhds 0 hr),
    mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hzr hz
  exact (heq z hz (by simpa [mem_ball_zero_iff] using hzr)).symm

/-- Changing the base point translates the quadratic constant by the same constant as the
primitive. -/
theorem schwarzChristoffelQuadraticConstantAtInfinity_change_base
    (a e : ι → ℝ) (b c : UpperHalfPlane) (hsum : ∑ i, e i = 1) :
    schwarzChristoffelQuadraticConstantAtInfinity a e b =
      schwarzChristoffelQuadraticConstantAtInfinity a e c -
        schwarzChristoffelPrimitive a e c b := by
  refine tendsto_nhds_unique
    (tendsto_schwarzChristoffelPrimitive_sub_quadratic_atInfinity_of_sum_eq_one a e b hsum) ?_
  refine Tendsto.congr' ?_
    ((tendsto_schwarzChristoffelPrimitive_sub_quadratic_atInfinity_of_sum_eq_one a e c
      hsum).sub tendsto_const_nhds)
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
  rw [schwarzChristoffelPrimitive_change_base a e b c hz]
  ring

/-! ### Quadratic asymptotics on the boundary -/

/-- Suppose the primitive minus a comparison function `P` equals `H (-1 / z)` near infinity in
the upper half-plane, with `H` holomorphic near zero, and `p x` is the boundary limit of `P` at
`x`. Then the boundary value minus `p x` tends to `H 0` along every filter on which `|x|` tends
to infinity. -/
private theorem tendsto_schwarzChristoffelBoundary_sub_of_eq_comp_neg_inv
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {P : ℂ → ℂ} {H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hH : DifferentiableOn ℂ H (ball 0 r))
    (heq : ∀ z ∈ upperHalfPlaneSet, ‖z⁻¹‖ < r →
      schwarzChristoffelPrimitive a e z₀ z - P z = H (-z⁻¹))
    {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) {p : ℝ → ℂ}
    (hp : ∀ᶠ x : ℝ in l, Tendsto P (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (p x))) :
    Tendsto (fun x => schwarzChristoffelBoundary a e z₀ x - p x) l (𝓝 (H 0)) := by
  have hinv : Tendsto (fun x : ℝ => -((x : ℂ))⁻¹) l (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hl).ofReal.neg
    simpa [Function.comp_def, ← abs_inv] using
      (tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Function.comp_def] using h.norm))
  refine (((hH 0 (mem_ball_self hr)).differentiableAt
    (ball_mem_nhds 0 hr)).continuousAt.tendsto.comp hinv).congr' ?_
  filter_upwards [hp, hinv.eventually (ball_mem_nhds 0 hr),
    hl.eventually_gt_atTop (∑ i, |a i|), hl.eventually_gt_atTop 0] with x hpx hxr hxa hx0
  have hx0' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (abs_pos.mp hx0)
  -- Beyond every prevertex the fibre over `x` is empty, so the boundary value is a limit.
  have hfibre : ∑ i with a i = x, e i = 0 := Finset.sum_eq_zero fun i hi => by
    have hai : |a i| ≤ ∑ j, |a j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    rw [(Finset.mem_filter.mp hi).2] at hai
    exact absurd hai (not_le.mpr hxa)
  have hB := (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x
    (hfibre ▸ neg_one_lt_zero)).sub hpx
  have hxr' : ‖((x : ℂ))⁻¹‖ < r := by simpa [mem_ball_zero_iff] using hxr
  -- Near `x`, the remainder is `H (-1 / z)`, which is continuous at `-1 / x`.
  have hHx : Tendsto (fun z : ℂ => H (-z⁻¹)) (𝓝[upperHalfPlaneSet] (x : ℂ))
      (𝓝 (H (-((x : ℂ))⁻¹))) := by
    have hcont : ContinuousAt (fun z : ℂ => -z⁻¹) (x : ℂ) :=
      (continuousAt_inv₀ hx0').neg
    have hHc : ContinuousAt H (-((x : ℂ))⁻¹) :=
      ((hH _ (by simpa [mem_ball_zero_iff] using hxr')).differentiableAt
        (isOpen_ball.mem_nhds (by simpa [mem_ball_zero_iff] using hxr'))).continuousAt
    exact (hHc.tendsto.comp hcont.tendsto).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ),
      schwarzChristoffelPrimitive a e z₀ z - P z = H (-z⁻¹) := by
    have hnorm : ∀ᶠ z in 𝓝 (x : ℂ), ‖z⁻¹‖ < r :=
      (continuousAt_inv₀ hx0').norm.eventually (gt_mem_nhds hxr')
    filter_upwards [nhdsWithin_le_nhds hnorm, self_mem_nhdsWithin] with z hzr hz
    exact heq z hz hzr
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
  exact (tendsto_nhds_unique (hB.congr' hnear) hHx).symm

/-- On the right outer edge, the normalized Schwarz--Christoffel boundary with total exponent
one has the asymptotic `x ^ 2 / 2 - M * x + C * log x + c`, where `c` is the quadratic
constant at infinity. -/
theorem tendsto_schwarzChristoffelBoundary_sub_quadratic_atTop_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = 1) :
    Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x -
      ((x : ℂ) ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * x +
        ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 *
          (Real.log x : ℂ)))
      atTop (𝓝 (schwarzChristoffelQuadraticConstantAtInfinity a e z₀)) := by
  obtain ⟨H, r, hr, hH, hH0, heq⟩ :=
    exists_differentiableOn_eq_comp_neg_inv_and_eq_quadraticConstantAtInfinity a e z₀ hsum
  rw [← hH0]
  refine tendsto_schwarzChristoffelBoundary_sub_of_eq_comp_neg_inv a e z₀ hr hH heq
    tendsto_abs_atTop_atTop ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hslit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hcont : ContinuousAt (fun z : ℂ => z ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * z +
      ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 * log z)
      (x : ℂ) := by
    fun_prop (disch := exact hslit)
  rw [ofReal_log hx.le]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- On the left outer edge, the normalized Schwarz--Christoffel boundary with total exponent
one has the asymptotic `x ^ 2 / 2 - M * x + C * log (-x) + c + C * π * I`. The extra term comes
from the argument `π` of the principal logarithm's boundary value from the upper half-plane on
the negative real axis. -/
theorem tendsto_schwarzChristoffelBoundary_sub_quadratic_atBot_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = 1) :
    Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x -
      ((x : ℂ) ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * x +
        ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 *
          (Real.log (-x) : ℂ)))
      atBot (𝓝 (schwarzChristoffelQuadraticConstantAtInfinity a e z₀ +
        ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 *
          (Real.pi * Complex.I))) := by
  obtain ⟨H, r, hr, hH, hH0, heq⟩ :=
    exists_differentiableOn_eq_comp_neg_inv_and_eq_quadraticConstantAtInfinity a e z₀ hsum
  set M : ℂ := ∑ i, (e i : ℂ) * (a i : ℂ)
  set C : ℂ := (M ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2
  have h := tendsto_schwarzChristoffelBoundary_sub_of_eq_comp_neg_inv a e z₀ hr hH heq
    tendsto_abs_atBot_atTop (p := fun x : ℝ =>
      (x : ℂ) ^ 2 / 2 - M * x + C * ((Real.log (-x) : ℂ) + Real.pi * Complex.I)) ?_
  · rw [hH0] at h
    refine (h.add_const (C * (Real.pi * Complex.I))).congr fun x => ?_
    ring
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  -- The principal logarithm has boundary value `log |x| + π * I` from above at `x < 0`.
  have hlog : Tendsto log (𝓝[upperHalfPlaneSet] (x : ℂ))
      (𝓝 ((Real.log (-x) : ℂ) + Real.pi * Complex.I)) := by
    have h := tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (z := (x : ℂ)) (by simpa using hx) (by simp)
    rw [norm_real, Real.norm_eq_abs, abs_of_neg hx] at h
    exact h.mono_left (nhdsWithin_mono _ fun _ hz => le_of_lt (α := ℝ) hz)
  have hpoly : Continuous fun z : ℂ => z ^ 2 / 2 - M * z := by fun_prop
  exact (hpoly.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).add (hlog.const_mul C)

/-! ### The outer sides of an end of opening `2π` -/

/-- The quadratic comparison terms are real at real arguments, for any real value of the
logarithm. -/
private theorem im_quadratic_ofReal (a e : ι → ℝ) (x y : ℝ) :
    ((x : ℂ) ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * x +
      ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 *
        (y : ℂ)).im = 0 := by
  have h : (x : ℂ) ^ 2 / 2 - (∑ i, (e i : ℂ) * (a i : ℂ)) * x +
      ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 * (y : ℂ) =
      ((x ^ 2 / 2 - (∑ i, e i * a i) * x +
        ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2 * y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, ofReal_im]

/-- The right outer side of a Schwarz--Christoffel boundary with total exponent one lies exactly
at the height of the quadratic constant at infinity. Only integrability at its finite endpoint is
needed. -/
theorem im_schwarzChristoffelBoundary_of_forall_le_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hsum : ∑ i, e i = 1) :
    (schwarzChristoffelBoundary a e z₀ p).im =
      (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im := by
  have hheight : ∀ x ∈ Ici p,
      (schwarzChristoffelBoundary a e z₀ x).im =
        (schwarzChristoffelBoundary a e z₀ p).im := by
    intro x hx
    have hmem := mem_image_of_mem (schwarzChristoffelBoundary a e z₀) hx
    rw [schwarzChristoffelBoundary_image_Ici_eq_ray a e z₀ hp ha (by rw [hsum]; norm_num)]
      at hmem
    obtain ⟨t, _, ht⟩ := hmem
    simpa using (congrArg Complex.im ht).symm
  -- A constant height agrees with its limit, since the comparison terms are real.
  have hlimit := (Complex.continuous_im.tendsto _).comp
    (tendsto_schwarzChristoffelBoundary_sub_quadratic_atTop_of_sum_eq_one a e z₀ hsum)
  apply tendsto_nhds_unique (l := atTop)
    (f := fun _ : ℝ => (schwarzChristoffelBoundary a e z₀ p).im) tendsto_const_nhds
  refine hlimit.congr' ?_
  filter_upwards [eventually_ge_atTop p] with x hx
  simp only [Function.comp_apply, sub_im, im_quadratic_ofReal, sub_zero]
  exact hheight x hx

/-- The left outer side of a Schwarz--Christoffel boundary with total exponent one lies exactly
`π * C` above the height of the quadratic constant at infinity, where
`C = ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2`. Only integrability at its finite endpoint
is needed. -/
theorem im_schwarzChristoffelBoundary_of_forall_ge_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) (hsum : ∑ i, e i = 1) :
    (schwarzChristoffelBoundary a e z₀ p).im =
      (schwarzChristoffelQuadraticConstantAtInfinity a e z₀).im +
        Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2) := by
  have hheight : ∀ x ∈ Iic p,
      (schwarzChristoffelBoundary a e z₀ x).im =
        (schwarzChristoffelBoundary a e z₀ p).im := by
    intro x hx
    have hmem := mem_image_of_mem (schwarzChristoffelBoundary a e z₀) hx
    rw [schwarzChristoffelBoundary_image_Iic_eq_ray a e z₀ hp ha (by rw [hsum]; norm_num)]
      at hmem
    obtain ⟨t, _, ht⟩ := hmem
    simpa [hsum, Complex.exp_pi_mul_I] using (congrArg Complex.im ht).symm
  -- The upper boundary value of the logarithm contributes the height difference `π * C`.
  have hlimit := (Complex.continuous_im.tendsto _).comp
    (tendsto_schwarzChristoffelBoundary_sub_quadratic_atBot_of_sum_eq_one a e z₀ hsum)
  have hC : (((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 *
      (Real.pi * Complex.I)).im = Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2) := by
    have h : ((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 - ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2 *
        (Real.pi * Complex.I) =
        ((Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, mul_I_im, ofReal_re]
  rw [add_im, hC] at hlimit
  apply tendsto_nhds_unique (l := atBot)
    (f := fun _ : ℝ => (schwarzChristoffelBoundary a e z₀ p).im) tendsto_const_nhds
  refine hlimit.congr' ?_
  filter_upwards [eventually_le_atBot p] with x hx
  simp only [Function.comp_apply, sub_im, im_quadratic_ofReal, sub_zero]
  exact hheight x hx

/-- **The outer sides of an end of opening `2π`.** When the total exponent is one, the two outer
images of the Schwarz--Christoffel boundary are disjoint exactly when the logarithmic
coefficient `C = ((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2` is nonzero. Both are horizontal
rays pointing to the right, at heights differing by `π * C`; when `C = 0` they overlap. The finite
prevertices need not be ordered or distinct. -/
theorem disjoint_schwarzChristoffelBoundary_outer_images_iff_of_sum_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p q : ℝ}
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    (hleft : ∀ i, e i ≠ 0 → p ≤ a i) (hright : ∀ i, e i ≠ 0 → a i ≤ q)
    (hsum : ∑ i, e i = 1) :
    Disjoint (schwarzChristoffelBoundary a e z₀ '' Iic p)
        (schwarzChristoffelBoundary a e z₀ '' Ici q) ↔
      (∑ i, e i * a i) ^ 2 ≠ ∑ i, e i * a i ^ 2 := by
  set L := schwarzChristoffelBoundary a e z₀ p
  set R := schwarzChristoffelBoundary a e z₀ q
  have hleftImage : schwarzChristoffelBoundary a e z₀ '' Iic p =
      (fun t : ℝ => L + (t : ℂ)) '' Ici 0 := by
    simpa [hsum, Complex.exp_pi_mul_I] using
      schwarzChristoffelBoundary_image_Iic_eq_ray a e z₀ hp hleft (by rw [hsum]; norm_num)
  have hrightImage : schwarzChristoffelBoundary a e z₀ '' Ici q =
      (fun t : ℝ => R + (t : ℂ)) '' Ici 0 :=
    schwarzChristoffelBoundary_image_Ici_eq_ray a e z₀ hq hright (by rw [hsum]; norm_num)
  have hL := im_schwarzChristoffelBoundary_of_forall_ge_of_sum_eq_one a e z₀ hp hleft hsum
  have hR := im_schwarzChristoffelBoundary_of_forall_le_of_sum_eq_one a e z₀ hq hright hsum
  rw [hleftImage, hrightImage]
  constructor
  · -- If the heights agree, both rays contain the point above the larger real part.
    intro hdisj hC
    have hLR : L.im = R.im := by
      rw [hL, hR, hC, sub_self, zero_div, mul_zero, add_zero]
    have hmem : L + ((max 0 (R.re - L.re) : ℝ) : ℂ) ∈ (fun t : ℝ => L + (t : ℂ)) '' Ici 0 :=
      ⟨_, le_max_left _ _, rfl⟩
    refine disjoint_left.mp hdisj hmem ⟨max 0 (L.re - R.re), le_max_left _ _, ?_⟩
    apply Complex.ext
    · simp only [add_re, ofReal_re]
      rcases le_total L.re R.re with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
    · simp [hLR]
  · -- Otherwise the rays lie on distinct horizontal lines.
    intro hC
    rw [disjoint_left]
    rintro z ⟨s, _, rfl⟩ ⟨t, _, hz⟩
    have him := congrArg Complex.im hz
    simp only [add_im, ofReal_im, add_zero] at him
    rw [hL, hR] at him
    have hpi : Real.pi * (((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2) = 0 := by linarith
    rcases mul_eq_zero.mp hpi with h | h
    · exact Real.pi_ne_zero h
    · exact hC (by linarith)

/-- When the total exponent is one and the logarithmic coefficient
`((∑ i, e i * a i) ^ 2 - ∑ i, e i * a i ^ 2) / 2` is nonzero, a Schwarz--Christoffel boundary is
simple if bounded sides meet only at consecutive vertices and each outer ray meets the bounded
sides only at its finite endpoint. No additional intersection condition between the outer rays is
needed. -/
theorem schwarzChristoffelBoundary_injective_of_edge_intersections_of_sum_eq_one
    {n : ℕ} (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l) (hsum : ∑ k, e k = 1)
    (hC : (∑ k, e k * a k) ^ 2 ≠ ∑ k, e k * a k ^ 2)
    (hinter : ∀ (i j : Fin (n + 1)), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ)
    (hleft : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (fun t : ℝ => schwarzChristoffelVertex a e z₀ 0 + (t : ℂ)) '' Ici 0 →
        z = schwarzChristoffelVertex a e z₀ 0)
    (hright : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (fun t : ℝ => schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)) + (t : ℂ)) ''
        Ici 0 → z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))) :
    Function.Injective (schwarzChristoffelBoundary a e z₀) := by
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ => ha k.zero_le
  have hlast : ∀ k, e k ≠ 0 → a k ≤ a (Fin.last (n + 1)) := fun k _ => ha k.le_last
  have hS : -1 ≤ ∑ k, e k := by rw [hsum]; norm_num
  have houter := (disjoint_schwarzChristoffelBoundary_outer_images_iff_of_sum_eq_one a e z₀
    (hfinite 0) (hfinite _) hfirst hlast hsum).mpr hC
  rw [schwarzChristoffelBoundary_image_Iic_eq_ray_prevertex a e z₀ 0 (hfinite 0) hfirst hS,
    schwarzChristoffelBoundary_image_Ici_eq_ray_prevertex a e z₀ (Fin.last (n + 1))
      (hfinite _) hlast hS] at houter
  apply schwarzChristoffelBoundary_injective_of_edge_intersections a e z₀ ha hfinite
    hS hinter (hright := hright) (houter := houter)
  simpa [hsum, Complex.exp_pi_mul_I] using hleft

/-- **The band omitted by the quadratic comparison function.** For real `M` and `C < 0`, far out
in the upper half-plane, the comparison function `z ^ 2 / 2 - M * z + C * log z` takes no value
with real part greater than `1 / 2` and height strictly between `π * C + η` and `-η`. Its imaginary
part is `(re z - M) * im z + C * arg z`; inside the band `im z` is bounded, so Jordan's inequality
puts `arg z` near `0` or `π`, which pushes the imaginary part out of the band. -/
theorem exists_forall_im_quadratic_log_notMem_Ioo {M C η : ℝ} (hC : C < 0) (hη : 0 < η) :
    ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      1 / 2 < (z ^ 2 / 2 - (M : ℂ) * z + (C : ℂ) * log z).re →
        (z ^ 2 / 2 - (M : ℂ) * z + (C : ℂ) * log z).im ∉ Ioo (Real.pi * C + η) (-η) := by
  refine ⟨max 1 (max (-(Real.pi * C) + |M| + 1) (Real.pi ^ 2 * C ^ 2 / η + 1)),
    fun z hz hzR hre => ?_⟩
  have hQre : (z ^ 2 / 2 - (M : ℂ) * z + (C : ℂ) * log z).re =
      ((z.re - M) ^ 2 - z.im ^ 2) / 2 - M ^ 2 / 2 + C * Real.log ‖z‖ := by
    simp [sq, Complex.mul_re, log_re]
    ring
  have hQim : (z ^ 2 / 2 - (M : ℂ) * z + (C : ℂ) * log z).im =
      (z.re - M) * z.im + C * arg z := by
    simp [sq, Complex.mul_im, log_im]
    ring
  rw [hQre] at hre
  rw [hQim]
  rintro ⟨hlo, hhi⟩
  have h1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hzR
  have h2 : -(Real.pi * C) + |M| + 1 ≤ ‖z‖ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hzR
  have h3 : Real.pi ^ 2 * C ^ 2 / η + 1 ≤ ‖z‖ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hzR
  have hpi := Real.pi_pos
  have hn : 0 < ‖z‖ := zero_lt_one.trans_le h1
  have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg h1
  have harg0 : 0 ≤ arg z := arg_nonneg_iff.mpr hz.le
  have harg1 : arg z ≤ Real.pi := arg_le_pi z
  -- The imaginary part is `(re z - M) * im z + C * arg z`. The real part forces
  -- `|re z - M| > 1`, and then the band forces `im z < -π * C`, so `arg z` is close to `0` or
  -- `π` by Jordan's inequality.
  have hs : 1 < |z.re - M| := by
    rw [← one_lt_sq_iff_one_lt_abs]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hC.le hlog, sq_nonneg M, sq_nonneg z.im]
  have hsy : |(z.re - M) * z.im| < -(Real.pi * C) := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hy : z.im < -(Real.pi * C) := by
    rw [abs_mul, abs_of_pos hz] at hsy
    nlinarith
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hz] at hnorm
  -- Since `‖z‖` is large, an angle bounded by Jordan's inequality costs less than `η`.
  have hratio : -C * (Real.pi / 2 * (z.im / ‖z‖)) < η := by
    -- Collect the factor `1 / ‖z‖` so that the denominator can be cleared.
    have hquot : -C * (Real.pi / 2 * (z.im / ‖z‖)) = -C * Real.pi * z.im / 2 / ‖z‖ := by ring
    rw [hquot, div_lt_iff₀ hn]
    have hηn : Real.pi ^ 2 * C ^ 2 + η ≤ η * ‖z‖ := by
      have := mul_le_mul_of_nonneg_left h3 hη.le
      rwa [mul_add, mul_div_cancel₀ _ hη.ne', mul_one] at this
    nlinarith [mul_pos (neg_pos.mpr hC) hpi]
  have hjordan (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) (hsin : Real.sin θ = z.im / ‖z‖) :
      θ ≤ Real.pi / 2 * (z.im / ‖z‖) := by
    have h := Real.mul_le_sin h0 h1
    rw [hsin, div_mul_eq_mul_div, div_le_iff₀ hpi] at h
    nlinarith
  rcases le_or_gt 0 z.re with hx | hx
  · -- Near the positive real axis, `C * arg z` is close to `0` and the linear term is positive.
    have hJ := hjordan (arg z) harg0 (arg_le_pi_div_two_iff.mpr (Or.inl hx)) (sin_arg z)
    have hsx : 0 < z.re - M := by
      rw [abs_of_nonneg hx] at hnorm
      linarith [le_abs_self M]
    nlinarith [mul_pos hsx hz, mul_le_mul_of_nonneg_left hJ (neg_nonneg.mpr hC.le)]
  · -- Near the negative real axis, `C * arg z` is close to `π * C` and the linear term is
    -- negative.
    have hhalf : Real.pi / 2 ≤ arg z := by
      by_contra! h
      rcases arg_lt_pi_div_two_iff.mp h with h | h | h
      · linarith
      · linarith
      · simp [h] at hz
    have hJ := hjordan (Real.pi - arg z) (by linarith) (by linarith)
      (by rw [Real.sin_pi_sub, sin_arg])
    have hsx : z.re - M < 0 := by
      rw [abs_of_neg hx] at hnorm
      linarith [neg_abs_le M]
    nlinarith [mul_neg_of_neg_of_pos hsx hz, mul_le_mul_of_nonneg_left hJ (neg_nonneg.mpr hC.le)]

end TauCeti
