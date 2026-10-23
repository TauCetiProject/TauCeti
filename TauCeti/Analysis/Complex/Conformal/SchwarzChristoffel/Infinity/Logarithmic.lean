/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Asymptotic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Basic
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

The same asymptotic holds for the canonical boundary values on the real axis beyond every
prevertex: the right end is asymptotic to `log x + c` and the left end to
`log (-x) + c + pi * I`, where `c` is the logarithmic constant at infinity. The term `pi * I`
is for the normalized primitive, whose integrand has leading coefficient one at infinity; an
affine postcomposition rotates and rescales it.

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

/-! ### Logarithmic asymptotics on the boundary -/

/-- Far from the prevertices, the normalized primitive moves little along the vertical segment
from height `s` up to height `1` above a real point. -/
private theorem norm_schwarzChristoffelPrimitive_add_I_sub_add_mul_I_le
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {C R : ℝ} (hC : 0 < C)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ →
      ‖schwarzChristoffelIntegrand a e z‖ ≤ C * ‖z‖ ^ (-1 : ℝ))
    {x : ℝ} (hx : max R 1 ≤ |x|) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ‖schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I) -
      schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ C / |x| := by
  have hxpos : 0 < |x| := zero_lt_one.trans_le ((le_max_right R 1).trans hx)
  have hxR : R ≤ |x| := (le_max_left R 1).trans hx
  have hmem : ∀ t ∈ Icc s 1, (x : ℂ) + (t : ℂ) * Complex.I ∈ upperHalfPlaneSet := by
    intro t ht
    simpa [upperHalfPlaneSet] using hs0.trans_le ht.1
  have hnorm (t : ℝ) : |x| ≤ ‖(x : ℂ) + (t : ℂ) * Complex.I‖ := by
    simpa using abs_re_le_norm ((x : ℂ) + (t : ℂ) * Complex.I)
  -- The integrand decays like `1 / ‖z‖`, and `|x| ≤ ‖z‖` along the whole segment.
  have hB : ∀ t ∈ Icc s 1,
      ‖Complex.I‖ * ‖schwarzChristoffelIntegrand a e ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C / |x| := by
    intro t _
    rw [norm_I, one_mul]
    calc
      ‖schwarzChristoffelIntegrand a e ((x : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ C * ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ^ (-1 : ℝ) := hbound _ (hxR.trans (hnorm t))
      _ ≤ C * |x| ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hxpos (hnorm t) (by norm_num)) hC.le
      _ = C / |x| := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hmove := norm_schwarzChristoffelPrimitive_sub_le_integral a e z₀ hs1 hmem hB
    intervalIntegrable_const
  rw [ofReal_one, one_mul, intervalIntegral.integral_const, smul_eq_mul] at hmove
  -- The segment has length at most one.
  exact hmove.trans (mul_le_of_le_one_left (div_nonneg hC.le hxpos.le) (by linarith))

/-- Far from the prevertices, a boundary value differs little from the value one unit directly
above it. This transfers the logarithmic asymptotic in the open half-plane to the boundary. -/
private theorem norm_schwarzChristoffelBoundary_sub_primitive_add_I_le
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {C R : ℝ} (hC : 0 < C)
    (hbound : ∀ z : ℂ, R ≤ ‖z‖ →
      ‖schwarzChristoffelIntegrand a e z‖ ≤ C * ‖z‖ ^ (-1 : ℝ))
    {x : ℝ} (hx : max R 1 ≤ |x|) (he : -1 < ∑ i with a i = x, e i) :
    ‖schwarzChristoffelBoundary a e z₀ x -
      schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I)‖ ≤ C / |x| := by
  let ε : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := by positivity
  have hεle (n : ℕ) : ε n ≤ 1 := inv_le_one_of_one_le₀ (by simp)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  -- Approach `x` vertically from inside the upper half-plane.
  have hpath : Tendsto (fun n => (x : ℂ) + (ε n : ℂ) * Complex.I) atTop
      (𝓝[upperHalfPlaneSet] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => by
      simpa [upperHalfPlaneSet] using hεpos n⟩
    simpa using tendsto_const_nhds.add
      (((Complex.continuous_ofReal.tendsto 0).comp hε).mul_const Complex.I)
  have hlimit := (((tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x he).comp
    hpath).const_sub (schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I))).norm
  rw [norm_sub_rev]
  exact le_of_tendsto hlimit (Eventually.of_forall fun n =>
    norm_schwarzChristoffelPrimitive_add_I_sub_add_mul_I_le a e z₀ hC hbound hx (hεpos n)
      (hεle n))

/-- Along any filter on which `|x|` tends to infinity, the normalized boundary value minus the
principal logarithm one unit above it tends to the logarithmic constant at infinity. -/
private theorem tendsto_schwarzChristoffelBoundary_sub_log_add_I
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) {l : Filter ℝ}
    (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x - log ((x : ℂ) + Complex.I)) l
      (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀)) := by
  obtain ⟨C, hC, R, _, hbound⟩ := exists_norm_schwarzChristoffelIntegrand_le_of_le_norm a e
  rw [hsum] at hbound
  have herror : Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x -
      schwarzChristoffelPrimitive a e z₀ ((x : ℂ) + Complex.I)) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_id.const_div_atTop C).comp hl)
    filter_upwards [hl.eventually_ge_atTop (max R 1), hl.eventually_gt_atTop (∑ i, |a i|)]
      with x hxR hxa
    -- Beyond every prevertex the fibre over `x` is empty.
    have hfibre : ∑ i with a i = x, e i = 0 := Finset.sum_eq_zero fun i hi => by
      have hai : |a i| ≤ ∑ j, |a j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
      rw [(Finset.mem_filter.mp hi).2] at hai
      exact absurd hai (not_le.mpr hxa)
    exact norm_schwarzChristoffelBoundary_sub_primitive_add_I_le a e z₀ hC hbound hxR
      (hfibre ▸ neg_one_lt_zero)
  have hpath : Tendsto (fun x : ℝ => (x : ℂ) + Complex.I) l
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp
      (tendsto_atTop_mono (fun x => ?_) hl),
      tendsto_principal.mpr (Eventually.of_forall fun x => by simp [upperHalfPlaneSet])⟩
    simpa using abs_re_le_norm ((x : ℂ) + Complex.I)
  simpa only [Function.comp_apply, sub_add_sub_cancel, zero_add] using
    herror.add ((tendsto_schwarzChristoffelPrimitive_sub_log_atInfinity a e z₀ hsum).comp hpath)

/-- On the right outer edge, the normalized Schwarz--Christoffel boundary has the asymptotic
`log x + c`, where `c` is its logarithmic constant at infinity. -/
theorem tendsto_schwarzChristoffelBoundary_sub_log_atTop_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x - (Real.log x : ℂ))
      atTop (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀)) := by
  have hsmall : Tendsto (fun x : ℝ => (1 : ℂ) + Complex.I / (x : ℂ)) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.ofReal.const_mul Complex.I).const_add (1 : ℂ)
  have hlogSmall : Tendsto (fun x : ℝ => log ((1 : ℂ) + Complex.I / (x : ℂ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.log_one] using
      (continuousAt_clog Complex.one_mem_slitPlane).tendsto.comp hsmall
  have hlog : Tendsto (fun x : ℝ => log ((x : ℂ) + Complex.I) - (Real.log x : ℂ))
      atTop (𝓝 0) := by
    refine hlogSmall.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hq : (1 : ℂ) + Complex.I / (x : ℂ) ≠ 0 := fun h => by
      simpa [div_im, hx.ne'] using congrArg Complex.im h
    -- Factor out the positive real `x` so that `log_ofReal_mul` splits the logarithm.
    have hfactor : (x : ℂ) + Complex.I = (x : ℂ) * (1 + Complex.I / (x : ℂ)) := by field_simp
    rw [hfactor, log_ofReal_mul hx hq]
    ring
  simpa only [sub_add_sub_cancel, add_zero] using
    (tendsto_schwarzChristoffelBoundary_sub_log_add_I a e z₀ hsum tendsto_abs_atTop_atTop).add
      hlog

/-- On the left outer edge, the normalized Schwarz--Christoffel boundary has the asymptotic
`log (-x) + c + pi * I`. The extra term comes from the argument `pi` of the principal logarithm's
boundary value from the upper half-plane on the negative real axis. -/
theorem tendsto_schwarzChristoffelBoundary_sub_log_neg_atBot_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hsum : ∑ i, e i = -1) :
    Tendsto (fun x : ℝ => schwarzChristoffelBoundary a e z₀ x - (Real.log (-x) : ℂ))
      atBot (𝓝 (schwarzChristoffelLogConstantAtInfinity a e z₀ + Real.pi * Complex.I)) := by
  let q : ℝ → ℂ := fun x => -1 + Complex.I / ((-x : ℝ) : ℂ)
  have hq : Tendsto q atBot (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hinv := (tendsto_inv_atTop_zero.comp Filter.tendsto_neg_atBot_atTop).ofReal
      have h := (hinv.const_mul Complex.I).const_add (-1 : ℂ)
      simpa [q, div_eq_mul_inv, Complex.ofReal_inv] using h
    · filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
      -- The imaginary part of `I / (-x)` is `-x / x ^ 2`, which is nonnegative for `x < 0`.
      have him : (q x).im = -x / (x * x) := by simp [q, Complex.div_im]
      rw [him]
      exact div_nonneg (neg_nonneg.mpr hx.le) (mul_self_nonneg x)
  have hlogSmall : Tendsto (fun x => log (q x)) atBot (𝓝 (Real.pi * Complex.I)) := by
    simpa only [Function.comp_def, norm_neg, norm_one, Real.log_one, ofReal_zero, zero_add] using
      (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
        (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp hq
  have hlog : Tendsto (fun x : ℝ => log ((x : ℂ) + Complex.I) -
      (Real.log (-x) : ℂ)) atBot (𝓝 (Real.pi * Complex.I)) := by
    refine hlogSmall.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    have hq0 : q x ≠ 0 := fun h => by
      simpa [q, div_im, hx.ne] using congrArg Complex.im h
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne
    -- Factor out the positive real `-x` so that `log_ofReal_mul` splits the logarithm.
    have hfactor : (x : ℂ) + Complex.I = ((-x : ℝ) : ℂ) * q x := by
      simp only [q]
      push_cast
      field_simp
      ring
    rw [hfactor, log_ofReal_mul (neg_pos.mpr hx) hq0]
    ring
  simpa only [sub_add_sub_cancel] using
    (tendsto_schwarzChristoffelBoundary_sub_log_add_I a e z₀ hsum tendsto_abs_atBot_atTop).add
      hlog

end TauCeti
