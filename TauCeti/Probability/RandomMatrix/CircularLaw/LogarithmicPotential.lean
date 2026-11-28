/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CircularLaw
public import TauCeti.Probability.RandomMatrix.CircularLaw.SelfConsistency

import TauCeti.MeasureTheory.Measure.ResolventTransform.LogIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic integral of the limiting shifted singular-value law

The scalar resolvent equation for the symmetrized singular-value law of a shifted Ginibre
matrix is given in Bordenave and Chafaï, *Around the circular law*, §4.5. A measure whose
imaginary transform satisfies this equation has mass one, a finite second moment and an
integrable logarithm. Its logarithmic integral equals the logarithmic potential of the
circular law at the shift. Since the real logarithm is even, this also gives the logarithmic
integral of the pushforward under absolute value used in Girko's hermitization.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

variable {μ : Measure ℝ} {r : ℝ}

/-- The imaginary-axis shifted singular-value equation forces a measure to have total mass one. -/
theorem isProbabilityMeasure_of_im_resolventTransform_eq_shiftedSingularValueResolventIm
    (haxis : ∀ t : ℝ, 0 < t →
      (resolventTransform μ (t * Complex.I)).im = shiftedSingularValueResolventIm r t) :
    IsProbabilityMeasure μ := by
  let t (n : ℕ) : ℝ := (n : ℝ) + 1
  let K (n : ℕ) (x : ℝ) := t n ^ 2 / (x ^ 2 + t n ^ 2)
  have ht : Tendsto t atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have ht₀ (n) : 0 < t n := by dsimp [t]; positivity
  have hK₀ (n : ℕ) : 0 ≤ᵐ[μ] K n := ae_of_all _ fun x ↦ by dsimp [K]; positivity
  have hlin (n : ℕ) : (∫ x, K n x ∂μ) = t n * shiftedSingularValueResolventIm r (t n) := by
    have him := haxis (t n) (ht₀ n)
    have hint : Integrable (resolvent (R := ℝ) (t n * Complex.I)) μ := by
      by_contra hn
      have hz : resolventTransform μ (t n * Complex.I) = 0 := by
        rw [resolventTransform_apply, integral_undef hn]
      rw [hz, Complex.zero_im] at him
      exact (shiftedSingularValueResolventIm_pos r (ht₀ n)).ne' him.symm
    have him' : (∫ x, t n / (x ^ 2 + t n ^ 2) ∂μ) =
        (resolventTransform μ (t n * Complex.I)).im := by
      simpa only [resolventTransform_apply, RCLike.im_eq_complex_im, Complex.im_resolvent_real,
        Complex.mul_I_im, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
        sub_zero] using integral_im hint
    rw [← him, ← him', ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by simp [K, mul_div_assoc, sq])
  have hki (n : ℕ) : Integrable (K n) μ := by
    by_contra hn
    have hz := integral_undef hn
    rw [hlin n] at hz
    exact (mul_pos (ht₀ n) (shiftedSingularValueResolventIm_pos r (ht₀ n))).ne' hz
  have hlim : Tendsto (fun n ↦ ∫ x, K n x ∂μ) atTop (𝓝 1) := by
    exact ((tendsto_mul_shiftedSingularValueResolventIm r).comp ht).congr fun n ↦ (hlin n).symm
  have hpoint := ae_of_all μ fun x ↦ (Real.tendsto_sq_div_sq_add_sq_atTop x).comp ht
  have htop : liminf (fun n ↦ ∫⁻ x, ‖K n x‖ₑ ∂μ) atTop ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2))
      (liminf_le_of_frequently_le' ?_)
    apply (hlim.eventually_le_const one_lt_two).frequently.mono
    intro n hn
    rw [← ofReal_integral_norm_eq_lintegral_eNorm (hki n),
      integral_congr_ae ((hK₀ n).mono fun _ hx ↦ Real.norm_of_nonneg hx)]
    exact ENNReal.ofReal_le_ofReal hn
  have hone : Integrable (fun _ : ℝ ↦ (1 : ℝ)) μ :=
    integrable_of_tendsto hpoint (fun n ↦ (hki n).aestronglyMeasurable) htop
  have : IsFiniteMeasure μ := (integrable_const_iff_isFiniteMeasure one_ne_zero).mp hone
  have hmass : Tendsto (fun n ↦ ∫ x, K n x ∂μ) atTop (𝓝 (μ.real univ)) := by
    have hDCT := tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
      (fun n ↦ (hki n).aestronglyMeasurable) hone (fun n ↦ (hK₀ n).mono fun x hx ↦ by
        rw [Real.norm_of_nonneg hx]
        exact (div_le_one (by positivity : 0 < x ^ 2 + t n ^ 2)).2
          (le_add_of_nonneg_left (sq_nonneg x))) hpoint
    simpa only [integral_const, smul_eq_mul, mul_one] using hDCT
  exact isProbabilityMeasure_iff_real.mpr (tendsto_nhds_unique hmass hlim)

private theorem sq_mul_one_sub_mul_shiftedSingularValueResolventIm_le (r : ℝ) {t : ℝ}
    (ht : 0 < t) :
    t ^ 2 * (1 - t * shiftedSingularValueResolventIm r t) ≤ 2 + r ^ 2 := by
  let u := shiftedSingularValueResolventIm r t
  let d := (t + u) ^ 2 + r ^ 2
  have hu : 0 ≤ u := shiftedSingularValueResolventIm_nonneg r t
  have hu' : u ≤ 1 := shiftedSingularValueResolventIm_le_one r t
  have hd : u * d = t + u := shiftedSingularValueResolventIm_mul_eq r ht.le
  have hd' : t ^ 2 ≤ d := by dsimp [d]; nlinarith
  have hid : d * (1 - t * u) = t * u + u ^ 2 + r ^ 2 := by
    dsimp [d] at hd ⊢
    linear_combination -t * hd
  have hnonneg : 0 ≤ 1 - t * u :=
    nonneg_of_mul_nonneg_right (hid ▸ (by positivity : 0 ≤ t * u + u ^ 2 + r ^ 2))
      ((sq_pos_of_pos ht).trans_le hd')
  have hsq : u ^ 2 ≤ 1 := by nlinarith
  calc
    t ^ 2 * (1 - t * u) ≤ d * (1 - t * u) := mul_le_mul_of_nonneg_right hd' hnonneg
    _ = t * u + u ^ 2 + r ^ 2 := hid
    _ ≤ 2 + r ^ 2 := by linarith

private theorem integral_truncated_sq_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) :
    (∫ x, t ^ 2 * (x ^ 2 / (x ^ 2 + t ^ 2)) ∂μ) =
      t ^ 2 * (1 - t * (resolventTransform μ (t * Complex.I)).im) := by
  have hb (x : ℝ) : t ^ 2 / (x ^ 2 + t ^ 2) ≤ 1 :=
    (div_le_one (by positivity)).2 (le_add_of_nonneg_left (sq_nonneg _))
  have hi : Integrable (fun x : ℝ ↦ t ^ 2 / (x ^ 2 + t ^ 2)) μ :=
    Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1 (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hb x)
  rw [integral_const_mul,
    ← integral_congr_ae (g := fun x : ℝ ↦ x ^ 2 / (x ^ 2 + t ^ 2)) (ae_of_all μ (fun x ↦
      show 1 - t ^ 2 / (x ^ 2 + t ^ 2) = x ^ 2 / (x ^ 2 + t ^ 2) by field_simp; ring)),
    integral_sub (integrable_const _) hi, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hmul : t * (resolventTransform μ (t * Complex.I)).im =
      ∫ x, t ^ 2 / (x ^ 2 + t ^ 2) ∂μ := by
    simpa using (mul_im_resolventTransform (μ := μ) (a := 0) (η := t))
  rw [hmul]

/-- A probability law satisfying the shifted singular-value equation on the imaginary axis
has finite second moment. -/
theorem integrable_sq_of_im_resolventTransform_eq_shiftedSingularValueResolventIm
    (haxis : ∀ t : ℝ, 0 < t →
      (resolventTransform μ (t * Complex.I)).im = shiftedSingularValueResolventIm r t) :
    Integrable (fun x : ℝ ↦ x ^ 2) μ := by
  have := isProbabilityMeasure_of_im_resolventTransform_eq_shiftedSingularValueResolventIm haxis
  let t (n : ℕ) : ℝ := (n : ℝ) + 1
  let G (n : ℕ) (x : ℝ) := t n ^ 2 * (x ^ 2 / (x ^ 2 + t n ^ 2))
  have ht₀ (n) : 0 < t n := by dsimp [t]; positivity
  have hG₀ (n) (x) : 0 ≤ G n x := by dsimp [G]; positivity
  have hG (n) : AEStronglyMeasurable (G n) μ :=
    (by unfold G; fun_prop : Measurable (G n)).aestronglyMeasurable
  refine integrable_of_tendsto (G := G) (ae_of_all _ fun x ↦ ?_) hG ?_
  · have ht : Tendsto t atTop atTop := tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop
    have hden := (((tendsto_inv_atTop_zero.comp ht).pow 2).const_mul (x ^ 2)).add_const 1
    have hg := (tendsto_const_nhds (x := x ^ 2)).div hden (by simp)
    norm_num at hg
    apply hg.congr
    intro n
    dsimp [G]
    field_simp [ne_of_gt (ht₀ n)]
  · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 + r ^ 2))
      (liminf_le_of_frequently_le' (.of_forall fun n ↦ ?_))
    have hint : Integrable (G n) μ := Integrable.of_bound (hG n) (t n ^ 2)
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_of_nonneg (hG₀ n x)]
        exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one (by positivity)).2
          (le_add_of_nonneg_right (sq_nonneg _))))
    rw [← ofReal_integral_norm_eq_lintegral_eNorm hint,
      integral_congr_ae (ae_of_all _ fun x ↦ Real.norm_of_nonneg (hG₀ n x))]
    exact ENNReal.ofReal_le_ofReal (by
      rw [integral_truncated_sq_eq μ (ht₀ n), haxis _ (ht₀ n)]
      exact sq_mul_one_sub_mul_shiftedSingularValueResolventIm_le r (ht₀ n))

private noncomputable def shiftedRegularizedLogIntegral (r t : ℝ) : ℝ :=
  Real.log ((t + shiftedSingularValueResolventIm r t) ^ 2 + r ^ 2) / 2 -
    shiftedSingularValueResolventIm r t ^ 2 / 2

private theorem hasDerivAt_shiftedRegularizedLogIntegral
    (haxis : ∀ t : ℝ, 0 < t →
      (resolventTransform μ (t * Complex.I)).im = shiftedSingularValueResolventIm r t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (shiftedRegularizedLogIntegral r) (shiftedSingularValueResolventIm r t) t := by
  have := isProbabilityMeasure_of_im_resolventTransform_eq_shiftedSingularValueResolventIm haxis
  let u := shiftedSingularValueResolventIm r
  have haxis' : (fun s : ℝ ↦ (resolventTransform μ (s * Complex.I)).im) =ᶠ[𝓝 t] u := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using haxis s hs
  have hu : DifferentiableAt ℝ u t := by
    have hm := (hasDerivAt_resolventTransform_of_im_ne_zero (μ := μ)
      (z := t * Complex.I) (by simpa using ht.ne')).differentiableAt.restrictScalars ℝ
    have ht' : DifferentiableAt ℝ (fun s : ℝ ↦ (s : ℂ) * Complex.I) t := by fun_prop
    exact (Complex.imCLM.differentiableAt.comp t (hm.comp t ht')).congr_of_eventuallyEq
      haxis'.symm
  have hs : HasDerivAt (fun s ↦ s + u s) (1 + deriv u t) t :=
    (hasDerivAt_id t).add hu.hasDerivAt
  have hd : HasDerivAt (fun s ↦ (s + u s) ^ 2 + r ^ 2)
      (2 * (t + u t) * (1 + deriv u t)) t := by simpa using (hs.pow 2).add_const (r ^ 2)
  have hu' : HasDerivAt (fun s ↦ u s ^ 2) (2 * u t * deriv u t) t := by
    simpa only [Pi.pow_def, Nat.cast_two, Nat.reduceSub, pow_one] using hu.hasDerivAt.pow 2
  have hpos : 0 < (t + u t) ^ 2 + r ^ 2 := by
    have := shiftedSingularValueResolventIm_nonneg r t
    dsimp [u]
    positivity
  have hdiv : u t = (t + u t) / ((t + u t) ^ 2 + r ^ 2) :=
    shiftedSingularValueResolventIm_eq_div r ht.le
  have heq : 2 * (t + u t) * (1 + deriv u t) / ((t + u t) ^ 2 + r ^ 2) / 2 -
      2 * u t * deriv u t / 2 = u t := by
    calc
      _ = ((t + u t) / ((t + u t) ^ 2 + r ^ 2)) * (1 + deriv u t) - u t * deriv u t := by
        ring
      _ = u t := by rw [← hdiv]; ring
  have hderiv : HasDerivAt (shiftedRegularizedLogIntegral r) _ t :=
    ((hd.log hpos.ne').div_const 2).sub (hu'.div_const 2)
  rwa [heq] at hderiv

private theorem tendsto_shiftedRegularizedLogIntegral_sub_log (r : ℝ) :
    Tendsto (fun t : ℝ ↦ shiftedRegularizedLogIntegral r t - Real.log t) atTop (𝓝 0) := by
  let u := shiftedSingularValueResolventIm r
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa using ((tendsto_mul_shiftedSingularValueResolventIm r).mul hinv).congr'
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
          rw [mul_comm t (u t), mul_inv_cancel_right₀ ht.ne'])
  have hterm : Tendsto (fun t : ℝ ↦ (1 + u t * t⁻¹) ^ 2 + (r * t⁻¹) ^ 2)
      atTop (𝓝 1) := by
    simpa using (((hu.mul hinv).const_add 1).pow 2).add ((hinv.const_mul r).pow 2)
  have hlim := (((Real.continuousAt_log one_ne_zero).tendsto.comp hterm).div_const 2).sub
    ((hu.pow 2).div_const 2)
  simp only [Real.log_one, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have haux : 0 < (1 + u t * t⁻¹) ^ 2 + (r * t⁻¹) ^ 2 := by
    have hu₀ : 0 ≤ u t := shiftedSingularValueResolventIm_nonneg r t
    positivity
  have hre : (t + u t) ^ 2 + r ^ 2 =
      t ^ 2 * ((1 + u t * t⁻¹) ^ 2 + (r * t⁻¹) ^ 2) := by field_simp
  simp only [Function.comp_apply]
  have heq : shiftedRegularizedLogIntegral r t =
      Real.log ((t + u t) ^ 2 + r ^ 2) / 2 - u t ^ 2 / 2 := rfl
  rw [heq, hre, Real.log_mul (by positivity) haux.ne', Real.log_pow]
  ring

/-- At positive height, the regularized logarithmic integral is determined explicitly by
the imaginary-axis solution of the shifted singular-value equation. -/
theorem integral_half_log_add_sq_of_im_resolventTransform_eq_shiftedSingularValueResolventIm
    (haxis : ∀ t : ℝ, 0 < t →
      (resolventTransform μ (t * Complex.I)).im = shiftedSingularValueResolventIm r t)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, Real.log (x ^ 2 + t ^ 2) / 2 ∂μ) =
      Real.log ((t + shiftedSingularValueResolventIm r t) ^ 2 + r ^ 2) / 2 -
        shiftedSingularValueResolventIm r t ^ 2 / 2 := by
  have := isProbabilityMeasure_of_im_resolventTransform_eq_shiftedSingularValueResolventIm haxis
  have hlog := integrable_log_sq_add_one
    (integrable_sq_of_im_resolventTransform_eq_shiftedSingularValueResolventIm haxis)
  have hf (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :=
    (haxis s hs) ▸ hasDerivAt_integral_half_log_add_sq hlog (ne_of_gt hs)
  have hg (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) := hasDerivAt_shiftedRegularizedLogIntegral haxis hs
  obtain ⟨a, ha⟩ := isOpen_Ioi.exists_eq_add_of_deriv_eq (convex_Ioi (0 : ℝ)).isPreconnected
    (fun s hs ↦ (hf s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hg s hs).differentiableAt.differentiableWithinAt)
    (fun s hs ↦ (hf s hs).deriv.trans (hg s hs).deriv.symm)
  have hlim := (tendsto_integral_half_log_add_sq_sub_log hlog).sub
    (tendsto_shiftedRegularizedLogIntegral_sub_log r)
  rw [sub_self] at hlim
  have ha' : Tendsto (fun _ : ℝ ↦ a) atTop (𝓝 0) := hlim.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hval : (∫ x, Real.log (x ^ 2 + s ^ 2) / 2 ∂μ) =
        shiftedRegularizedLogIntegral r s + a := ha hs
    rw [hval]
    ring)
  have hzero := tendsto_nhds_unique ha' tendsto_const_nhds
  simpa [shiftedRegularizedLogIntegral, ← hzero] using ha ht

private theorem tendsto_shiftedRegularizedLogIntegral_nhdsGT_zero (z : ℂ) :
    Tendsto (shiftedRegularizedLogIntegral ‖z‖) (𝓝[>] 0)
      (𝓝 (TauCeti.Probability.circularLaw.logarithmicPotential z)) := by
  let r := ‖z‖
  have hu := tendsto_shiftedSingularValueResolventIm_nhdsGT_zero r
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hsq : (√(1 - r ^ 2)) ^ 2 = max (1 - r ^ 2) 0 := Real.sq_sqrt'
  have hden : (√(1 - r ^ 2)) ^ 2 + r ^ 2 = max 1 (r ^ 2) := by
    rw [hsq, ← max_add_add_right]
    ring_nf
  have hsum := (((ht.add hu).pow 2).add_const (r ^ 2))
  rw [zero_add, hden] at hsum
  have hd : 0 < max 1 (r ^ 2) := zero_lt_one.trans_le (le_max_left _ _)
  have hlim := (((Real.continuousAt_log hd.ne').tendsto.comp hsum).div_const 2).sub
    ((hu.pow 2).div_const 2)
  have hlim' : Tendsto (shiftedRegularizedLogIntegral r) (𝓝[>] 0)
      (𝓝 (Real.log (max 1 (r ^ 2)) / 2 - (√(1 - r ^ 2)) ^ 2 / 2)) := hlim
  rcases lt_or_ge r 1 with hr | hr
  · rw [TauCeti.Probability.logarithmicPotential_circularLaw_of_norm_lt_one hr]
    have hr' : r ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [max_eq_left hr', Real.log_one, zero_div, hsq, max_eq_left (sub_nonneg.mpr hr'),
      zero_sub, ← neg_div, neg_sub] at hlim'
    exact hlim'
  · rw [TauCeti.Probability.logarithmicPotential_circularLaw_of_one_le_norm hr]
    have hr' : 1 ≤ r ^ 2 := by nlinarith
    rwa [max_eq_right hr', Real.log_pow, hsq, max_eq_right (sub_nonpos.mpr hr'), zero_div,
      sub_zero, Nat.cast_two, mul_div_cancel_left₀ _ (by norm_num)] at hlim'

/-- The logarithmic integral of a measure satisfying the imaginary-axis shifted
singular-value equation equals the logarithmic potential of the circular law at the shift.
The integral is absolutely convergent. -/
theorem integrable_log_and_integral_log_eq_logarithmicPotential_circularLaw (z : ℂ)
    (haxis : ∀ t : ℝ, 0 < t →
      (resolventTransform μ (t * Complex.I)).im = shiftedSingularValueResolventIm ‖z‖ t) :
    Integrable Real.log μ ∧
      (∫ x, Real.log x ∂μ) = TauCeti.Probability.circularLaw.logarithmicPotential z := by
  have := isProbabilityMeasure_of_im_resolventTransform_eq_shiftedSingularValueResolventIm haxis
  have hlog := integrable_log_sq_add_one
    (integrable_sq_of_im_resolventTransform_eq_shiftedSingularValueResolventIm haxis)
  have hb (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      (resolventTransform μ (t * Complex.I)).im ≤ 1 := by
    rw [haxis t ht.1]
    exact shiftedSingularValueResolventIm_le_one _ _
  obtain ⟨hint, htend⟩ := integrable_log_and_tendsto_integral_half_log_add_sq hlog hb
  refine ⟨hint, tendsto_nhds_unique htend
    ((tendsto_shiftedRegularizedLogIntegral_nhdsGT_zero z).congr' ?_)⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (integral_half_log_add_sq_of_im_resolventTransform_eq_shiftedSingularValueResolventIm
    haxis ht).symm

end TauCeti
