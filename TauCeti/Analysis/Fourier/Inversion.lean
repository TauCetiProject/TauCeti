/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion

import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
import TauCeti.Analysis.Fourier.RiemannLebesgue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fourier inversion and uniqueness

On a finite-dimensional real inner product space, a continuous integrable function whose Fourier
transform vanishes is zero. The vanishing transform is trivially integrable, so Mathlib's Fourier
inversion formula `Continuous.fourierInv_fourier_eq` applies and recovers the function as the
inverse transform of zero.

For a real source variable, the Dini criterion instead assumes integrability of a local
difference quotient. It recovers the function from symmetric finite inverse Fourier integrals even
when the Fourier transform is not integrable. If the source is differentiable with integrable
derivative, the partial inverse integrals are also bounded uniformly in the point and truncation
height, by a constant times the L1 norm of its derivative.

## Main results

* `Continuous.eq_zero_of_fourier_eq_zero`: a continuous integrable function with vanishing Fourier
  transform is zero.
* `MeasureTheory.Integrable.intervalIntegral_fourierInv_fourier_eq_integral_sinc`: the finite-height
  Dirichlet-kernel formula, for arbitrary real truncation height.
* `MeasureTheory.Integrable.tendsto_intervalIntegral_fourierInv_fourier`: pointwise norm
  convergence of symmetric truncations under the local Dini condition.
* `Real.exists_bound_intervalIntegral_fourierInv_fourier`: uniform control by the L1
  derivative norm.

## References

The finite-kernel and principal-value arguments adapt the work of Robby Sneiderman in
[PNT Laplace inversion](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/5754873e8dae73f3b50f8f2b7a4f0b15d4df58aa/PrimeNumberTheoremAnd/LaplaceInversion.lean).
The proof uses Mathlib's interval Fubini and Riemann--Lebesgue theorems and the symmetric
Dirichlet integral.
-/

public section

open MeasureTheory
open scoped FourierTransform

section Uniqueness

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : V → E}

/-- A continuous integrable function whose Fourier transform vanishes is zero. -/
theorem Continuous.eq_zero_of_fourier_eq_zero (h : Continuous f) (hf : Integrable f)
    (hF : 𝓕 f = 0) : f = 0 := by
  have hinv := h.fourierInv_fourier_eq hf (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  ext v
  simp [Real.fourierInv_eq]

end Uniqueness

open Filter Topology Real Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem integrable_kernel_prod {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℝ → F} (hf : Integrable f) (x T : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦ Complex.exp (((2 * π * z.1 * (x - z.2) : ℝ) : ℂ) * I) • f z.2)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
  let : IsFiniteMeasure (volume.restrict (Set.uIoc (-T) T)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      simpa only [Set.uIoc] using
        (measure_Ioc_lt_top (μ := volume) (a := min (-T) T) (b := max (-T) T))⟩
  have hn : Integrable (fun u ↦ ‖f u‖) :=
    hf.mono_eNorm hf.aestronglyMeasurable.norm (.of_forall fun _ ↦ by simp)
  refine (hn.comp_snd (volume.restrict (Set.uIoc (-T) T))).mono_eNorm ?_ ?_
  · exact (by fun_prop : Continuous (fun z : ℝ × ℝ ↦
      Complex.exp (((2 * π * z.1 * (x - z.2) : ℝ) : ℂ) * I)))
      |>.aestronglyMeasurable.smul hf.aestronglyMeasurable.comp_snd
  · filter_upwards with z
    rw [eNorm_le_iff_norm_le]
    simp only [norm_smul, norm_exp_ofReal_mul_I, norm_norm, one_mul, le_refl]

private theorem intervalIntegral_fourierInv_fourier_eq_integral_exp
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    (∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) =
      ∫ y, (∫ t in -T..T,
        Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I)) • f y := by
  by_cases hE : CompleteSpace E
  · let : CompleteSpace E := hE
    calc
      _ = ∫ t in -T..T, ∫ y,
          Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I) • f y := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [Real.fourier_real_eq_integral_exp_smul, Circle.smul_def, ← MeasureTheory.integral_smul]
        apply integral_congr_ae
        filter_upwards with y
        rw [← smul_assoc, smul_eq_mul, Real.fourierChar_apply, ← Complex.exp_add]
        apply congrArg (fun z : ℂ ↦ z • f y)
        apply congrArg Complex.exp
        push_cast
        ring
      _ = ∫ y, ∫ t in -T..T,
          Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I) • f y :=
        intervalIntegral_integral_swap (integrable_kernel_prod hf x T)
      _ = _ := by simp_rw [intervalIntegral.integral_smul_const]
  · simp [intervalIntegral, integral_of_not_completeSpace hE]

/-- The inverse Fourier integral over a finite symmetric frequency interval is convolution
with the sinc kernel. The formula holds for every real truncation height, with the usual
orientation of interval integrals. -/
theorem MeasureTheory.Integrable.intervalIntegral_fourierInv_fourier_eq_integral_sinc
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    ∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t =
      ∫ u, (2 * T * Real.sinc (2 * π * T * u) : ℂ) • f (x - u) := by
  rw [intervalIntegral_fourierInv_fourier_eq_integral_exp hf]
  calc
    _ = ∫ y, (2 * T * Real.sinc (2 * π * T * (x - y)) : ℂ) • f y := by
      apply integral_congr_ae
      filter_upwards with y
      congr 1
      have heq : (fun t : ℝ ↦ Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I)) =
          (fun t : ℝ ↦ Complex.exp (((t * (2 * π * (x - y)) : ℝ) : ℂ) * I)) := by
        ext t
        apply congrArg Complex.exp
        apply congrArg (fun r : ℝ ↦ (r : ℂ) * I)
        ring
      rw [heq]
      -- Factor out T so the zero-frequency phase is expressed in terms of ha.
      by_cases ha : 2 * π * (x - y) = 0
      · simp [ha, show 2 * π * T * (x - y) = T * (2 * π * (x - y)) by ring]
        ring
      · rw [intervalIntegral.integral_comp_mul_right
          (fun t : ℝ ↦ Complex.exp ((t : ℂ) * I)) ha,
          neg_mul, integral_exp_mul_I_eq_sinc]
        -- Match the endpoint times frequency returned by the scaled integral formula.
        rw [show 2 * π * T * (x - y) = T * (2 * π * (x - y)) by ring]
        simp only [Complex.real_smul]
        push_cast
        have hxy : x - y ≠ 0 := by
          intro h
          simp [h] at ha
        have hxyc : (x : ℂ) - (y : ℂ) ≠ 0 := by exact_mod_cast hxy
        field_simp [hxyc]
    _ = _ := by
      rw [← integral_sub_left_eq_self
        (fun y : ℝ ↦ (2 * T * Real.sinc (2 * π * T * (x - y)) : ℂ) • f y) volume x]
      simp only [sub_sub_cancel]

private theorem error_integrable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℝ → F} (hf : Integrable f) {x R : ℝ}
    (hR : 0 < R)
    (hq : IntegrableOn (fun u : ℝ ↦ (u : ℂ)⁻¹ • (f (x - u) - f x))
      (Set.Ioc (-R) R)) :
    Integrable (fun u : ℝ ↦ (Set.Ioc (-R) R).indicator
      (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
      (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u) := by
  have hi := (integrable_indicator_iff measurableSet_Ioc).mpr hq
  have hn : Integrable (fun u ↦ ‖f u‖) :=
    hf.mono_eNorm hf.aestronglyMeasurable.norm (.of_forall fun _ ↦ by simp)
  have hb : ∀ u : ℝ,
      ‖((Set.Ioc (-R) R)ᶜ.indicator (fun u : ℝ ↦ (u : ℂ)⁻¹) u)‖ ≤ R⁻¹ := by
    intro u
    by_cases hu : u ∈ Set.Ioc (-R) R
    · simp only [Set.mem_compl_iff, not_not, hu, Set.indicator_of_notMem, norm_zero]
      exact inv_nonneg.mpr hR.le
    · rw [Set.indicator_of_mem hu, norm_inv, norm_real, Real.norm_eq_abs]
      apply inv_anti₀ hR
      rcases not_and_or.mp hu with hu | hu
      · exact (neg_le_abs u).trans' (by linarith [not_lt.mp hu])
      · exact (le_abs_self u).trans' (not_le.mp hu).le
  have ht : Integrable (fun u : ℝ ↦
      ((Set.Ioc (-R) R)ᶜ.indicator (fun u : ℝ ↦ (u : ℂ)⁻¹) u) • f (x - u)) := by
    refine ((hn.comp_sub_left x).const_mul R⁻¹).mono_eNorm ?_ ?_
    · exact ((by fun_prop : Measurable (fun u : ℝ ↦ (u : ℂ)⁻¹)).indicator
        measurableSet_Ioc.compl).aestronglyMeasurable.smul
          (hf.1.comp_measurePreserving (volume.measurePreserving_sub_left x))
    · filter_upwards with u
      rw [eNorm_le_iff_norm_le, norm_smul, Real.norm_of_nonneg
        (mul_nonneg (inv_nonneg.mpr hR.le) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)
  have heq : (fun u : ℝ ↦
      ((Set.Ioc (-R) R)ᶜ.indicator (fun u : ℝ ↦ (u : ℂ)⁻¹) u) • f (x - u)) =
      (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) := by
    ext u
    by_cases hu : u ∈ Set.Ioc (-R) R <;> simp [hu]
  rw [heq] at ht
  exact hi.add ht

private theorem window_mass {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ ↦ ∫ u in -R..R, Real.sin (2 * π * T * u) / (π * u))
      atTop (nhds 1) := by
  have H := (TauCeti.Contour.tendsto_integral_sin_mul_div_neg_self_atTop (a := 1) zero_lt_one).comp
    ((tendsto_id.const_mul_atTop (by positivity : 0 < 2 * π * R)))
  have H' := H.const_mul π⁻¹
  simp only [one_mul, inv_mul_cancel₀ Real.pi_ne_zero] at H'
  apply H'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  dsimp only [Function.comp_apply, id_eq]
  -- Put both endpoints in the scaled form required by the interval substitution theorem.
  rw [show 2 * π * R * T = R * (2 * π * T) by ring,
    show -(R * (2 * π * T)) = (-R) * (2 * π * T) by ring,
    ← intervalIntegral.smul_integral_comp_mul_right]
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  field_simp

private theorem kernel_eq {u : ℝ} (hu : u ≠ 0) (T : ℝ) :
    2 * T * Real.sinc (2 * π * T * u) = Real.sin (2 * π * T * u) / (π * u) := by
  by_cases hT : T = 0
  · simp [hT]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hT) hu)]
    field_simp

private theorem sinc_kernel_ae_eq (T : ℝ) :
    (fun u : ℝ ↦ (2 * T * Real.sinc (2 * π * T * u) : ℂ)) =ᵐ[volume]
      fun u ↦ (Real.sin (2 * π * T * u) / (π * u) : ℂ) := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
  exact_mod_cast kernel_eq (by simpa using hu) T

private theorem integrable_window_kernel (R T : ℝ) :
    Integrable ((Set.Ioc (-R) R).indicator
      (fun u : ℝ ↦ (Real.sin (2 * π * T * u) / (π * u) : ℂ))) := by
  have hc : Continuous (fun u : ℝ ↦ (2 * T * Real.sinc (2 * π * T * u) : ℂ)) := by fun_prop
  have H : Integrable ((Set.Ioc (-R) R).indicator
      (fun u : ℝ ↦ (2 * T * Real.sinc (2 * π * T * u) : ℂ))) :=
    (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  apply H.congr
  filter_upwards [sinc_kernel_ae_eq T] with u hu
  by_cases hs : u ∈ Set.Ioc (-R) R <;> simp [hs, hu]

private theorem sine_quotient_split {F : Type*} [AddCommGroup F] [Module ℂ F]
    (f : ℝ → F) (x R T u : ℝ) :
    (Real.sin (2 * π * T * u) : ℂ) •
      ((Set.Ioc (-R) R).indicator (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
       (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u) =
    (π : ℂ) • ((Real.sin (2 * π * T * u) / (π * u) : ℂ) • f (x - u) -
      (Set.Ioc (-R) R).indicator
        (fun u : ℝ ↦ (Real.sin (2 * π * T * u) / (π * u) : ℂ)) u • f x) := by
  by_cases hu : u = 0
  · simp [hu]
  have hc : (π : ℂ) * (Real.sin (2 * π * T * u) / (π * u) : ℂ) =
      (Real.sin (2 * π * T * u) : ℂ) * (u : ℂ)⁻¹ := by
    field_simp
  by_cases hs : u ∈ Set.Ioc (-R) R
  · have hsc : u ∉ (Set.Ioc (-R) R)ᶜ := by simpa using hs
    simp only [Set.indicator_of_mem hs, Set.indicator_of_notMem hsc, add_zero,
      smul_sub, ← smul_assoc, smul_eq_mul, hc]
  · have hsc : u ∈ (Set.Ioc (-R) R)ᶜ := hs
    simp only [Set.indicator_of_notMem hs, Set.indicator_of_mem hsc, zero_add,
      zero_smul, sub_zero, ← smul_assoc, smul_eq_mul, hc]

private theorem integrable_raw_kernel {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℝ → F} (hf : Integrable f) (x T : ℝ) :
    Integrable (fun u : ℝ ↦ (Real.sin (2 * π * T * u) / (π * u) : ℂ) • f (x - u)) := by
  have hn : Integrable (fun u ↦ ‖f u‖) :=
    hf.mono_eNorm hf.aestronglyMeasurable.norm (.of_forall fun _ ↦ by simp)
  have H : Integrable (fun u : ℝ ↦ (2 * T * Real.sinc (2 * π * T * u) : ℂ) • f (x - u)) := by
    refine ((hn.comp_sub_left x).const_mul (2 * |T|)).mono_eNorm ?_ ?_
    · exact (by fun_prop : Continuous (fun u : ℝ ↦
        (2 * T * Real.sinc (2 * π * T * u) : ℂ))).aestronglyMeasurable.smul
          (hf.1.comp_measurePreserving (volume.measurePreserving_sub_left x))
    · filter_upwards with u
      rw [eNorm_le_iff_norm_le, norm_smul, Real.norm_of_nonneg
        (mul_nonneg (by positivity) (norm_nonneg _))]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simp only [norm_mul, Complex.norm_ofNat, norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)
  apply H.congr
  filter_upwards [sinc_kernel_ae_eq T] with u hk
  rw [hk]

private theorem kernel_split [CompleteSpace E] {f : ℝ → E} (hf : Integrable f)
    {x R : ℝ} (hR : 0 ≤ R) (T : ℝ) :
    (∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) =
      (π : ℂ)⁻¹ • (∫ u, (Real.sin (2 * π * T * u) : ℂ) •
        ((Set.Ioc (-R) R).indicator (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
         (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u)) +
      ((∫ u in -R..R, Real.sin (2 * π * T * u) / (π * u) : ℝ) : ℂ) • f x := by
  have hi : Integrable (fun u ↦ (Real.sin (2 * π * T * u) : ℂ) •
      ((Set.Ioc (-R) R).indicator (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
       (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u)) := by
    apply (((integrable_raw_kernel hf x T).sub
      ((integrable_window_kernel R T).smul_const (f x))).smul (π : ℂ)).congr
    exact Filter.Eventually.of_forall (fun u ↦ (sine_quotient_split f x R T u).symm)
  rw [hf.intervalIntegral_fourierInv_fourier_eq_integral_sinc, ← integral_smul,
    intervalIntegral.integral_of_le (by linarith),
    ← _root_.integral_complex_ofReal, ← integral_smul_const,
    ← integral_indicator measurableSet_Ioc]
  simp_rw [Set.indicator_smul_const_apply, Complex.ofReal_div, Complex.ofReal_mul]
  rw [← integral_add]
  · apply integral_congr_ae
    filter_upwards [sinc_kernel_ae_eq T] with u hk
    rw [hk, sine_quotient_split]
    simp only [← smul_assoc, smul_eq_mul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_smul]
    module
  · exact hi.smul ((π : ℂ)⁻¹)
  · exact (integrable_window_kernel R T).smul_const (f x)

/-- **Dini Fourier inversion** from an integrable local difference quotient.
Neither continuity at the evaluation point nor integrability of the Fourier transform is assumed.
The value of the quotient at zero is immaterial. -/
theorem MeasureTheory.Integrable.tendsto_intervalIntegral_fourierInv_fourier
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) {x R : ℝ}
    (hR : R ≠ 0)
    (hq : IntervalIntegrable (fun u : ℝ ↦ (u : ℂ)⁻¹ • (f (x - u) - f x))
      volume (-R) R) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) atTop (nhds (f x)) := by
  have hR' : 0 < |R| := abs_pos.mpr hR
  have hq' : IntervalIntegrable (fun u : ℝ ↦ (u : ℂ)⁻¹ • (f (x - u) - f x))
      volume (-|R|) |R| := by
    rcases lt_or_gt_of_ne hR with hneg | hpos
    · simpa only [abs_of_neg hneg, neg_neg] using hq.symm
    · simpa only [abs_of_pos hpos] using hq
  have H := ((error_integrable hf hR' hq'.1).tendsto_integral_sin_smul_atTop.const_smul
    (π : ℂ)⁻¹).add
    ((Complex.continuous_ofReal.tendsto 1 |>.comp (window_mass hR')).smul_const (f x))
  simp only [smul_zero, Complex.ofReal_one, one_smul, zero_add] at H
  exact H.congr (fun T ↦ (kernel_split hf hR'.le T).symm)

private theorem hasDerivAt_sinc_primitive (T u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (((∫ t in (0 : ℝ)..(2 * π * T * v), Real.sinc t) / π : ℝ) : ℂ))
      (2 * T * Real.sinc (2 * π * T * u) : ℂ) u := by
  have H : HasDerivAt
      (fun v : ℝ ↦ (∫ t in (0 : ℝ)..(2 * π * T * v), Real.sinc t) / π)
      (Real.sinc (2 * π * T * u) * (2 * π * T) / π) u := by
    simpa only [Function.comp_apply, mul_one] using
      ((Real.continuous_sinc.integral_hasStrictDerivAt 0 (2 * π * T * u)).hasDerivAt.comp u
        ((hasDerivAt_id u).const_mul (2 * π * T))).div_const π
  have H' := H.ofReal_comp
  convert H' using 1
  push_cast
  field_simp

private theorem continuous_sinc_primitive (T : ℝ) :
    Continuous (fun u : ℝ ↦ (((∫ t in (0 : ℝ)..(2 * π * T * u), Real.sinc t) / π : ℝ) : ℂ)) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_sinc_primitive T u).continuousAt

private theorem norm_sinc_primitive_le {M : ℝ}
    (hM : ∀ z : ℝ, ‖∫ t in (0 : ℝ)..z, Real.sinc t‖ ≤ M) (T u : ℝ) :
    ‖(((∫ t in (0 : ℝ)..(2 * π * T * u), Real.sinc t) / π : ℝ) : ℂ)‖ ≤ M / π := by
  simp only [norm_real, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right
    (by simpa only [Real.norm_eq_abs] using hM (2 * π * T * u)) Real.pi_pos.le

private theorem integral_kernel_eq {f : ℝ → E} (hfd : Differentiable ℝ f)
    (hf : Integrable f) (hd : Integrable (deriv f)) (x T : ℝ) :
    (∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) =
      ∫ u, (((∫ t in (0 : ℝ)..(2 * π * T * u), Real.sinc t) / π : ℝ) : ℂ) •
        deriv f (x - u) := by
  obtain ⟨M, _, hM⟩ := Real.exists_norm_integral_sinc_le
  let U : ℝ → ℂ := fun u ↦ ((∫ t in (0 : ℝ)..(2 * π * T * u), Real.sinc t) / π : ℝ)
  let U' : ℝ → ℂ := fun u ↦ (2 * T * Real.sinc (2 * π * T * u) : ℂ)
  let V : ℝ → E := fun u ↦ f (x - u)
  let V' : ℝ → E := fun u ↦ -deriv f (x - u)
  have hu (u : ℝ) : HasDerivAt U (U' u) u := hasDerivAt_sinc_primitive T u
  have hv (u : ℝ) : HasDerivAt V (V' u) u := by
    simpa only [V, V', Function.comp_def, neg_one_smul] using!
      (hfd (x - u)).hasDerivAt.scomp u ((hasDerivAt_id u).const_sub x)
  have hU (u : ℝ) : ‖U u‖ ≤ M / π := norm_sinc_primitive_le hM T u
  have hK (u : ℝ) : ‖U' u‖ ≤ 2 * |T| := by
    simp only [U', norm_mul, Complex.norm_ofNat, norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)
  have hVi : Integrable V := hf.comp_sub_left x
  have hV'i : Integrable V' := (hd.comp_sub_left x).neg
  have hUi : Integrable (fun u ↦ U u • V u) := hVi.bdd_smul (φ := U) (M / π)
    ((continuous_sinc_primitive T).aestronglyMeasurable)
    (Eventually.of_forall hU)
  have hUV' : Integrable (fun u ↦ U u • V' u) := hV'i.bdd_smul (φ := U) (M / π)
    ((continuous_sinc_primitive T).aestronglyMeasurable)
    (Eventually.of_forall hU)
  have hU'V : Integrable (fun u ↦ U' u • V u) := hVi.bdd_smul (φ := U') (2 * |T|) (by fun_prop)
    (Eventually.of_forall hK)
  have heq := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℂ) (fun u _ ↦ hu u) (fun u _ ↦ hv u) hUV' hU'V hUi
  simp only [ContinuousLinearMap.lsmul_apply] at heq
  rw [hf.intervalIntegral_fourierInv_fourier_eq_integral_sinc]
  have heq' : (∫ u, U' u • V u) = -(∫ u, U u • V' u) := by
    simpa only [neg_neg] using (congrArg Neg.neg heq).symm
  simpa only [U, U', V, V', smul_neg, integral_neg, neg_neg] using heq'

/-- Symmetric partial inverse Fourier integrals are bounded uniformly in the evaluation point
and every real truncation height by a constant times the L1 norm of the derivative.
The constant is independent of the source function. Neither source integrability nor
completeness is assumed; nonintegrable Fourier integrals use the usual totalized value. -/
theorem Real.exists_bound_intervalIntegral_fourierInv_fourier :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℝ → E}, Differentiable ℝ f → Integrable (deriv f) →
      ∀ x T : ℝ, ‖∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t‖ ≤ C * ∫ u, ‖deriv f u‖ := by
  obtain ⟨M, hM0, hM⟩ := Real.exists_norm_integral_sinc_le
  have hC : 0 ≤ M / π := div_nonneg hM0 Real.pi_pos.le
  refine ⟨M / π, hC, fun {f} hf hd x T ↦ ?_⟩
  by_cases hI : Integrable f
  · rw [integral_kernel_eq hf hI hd]
    have hi : Integrable (fun u : ℝ ↦
        (((∫ t in (0 : ℝ)..(2 * π * T * u), Real.sinc t) / π : ℝ) : ℂ) • deriv f (x - u)) :=
      (hd.comp_sub_left x).bdd_smul (M / π)
      ((continuous_sinc_primitive T).aestronglyMeasurable)
      (Eventually.of_forall (norm_sinc_primitive_le hM T))
    calc
      _ ≤ ∫ u, ‖(((∫ t in (0 : ℝ)..(2 * π * T * u), Real.sinc t) / π : ℝ) : ℂ) •
          deriv f (x - u)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u, (M / π) * ‖deriv f (x - u)‖ := by
        apply integral_mono hi.norm (((hd.comp_sub_left x).norm).const_mul (M / π))
        intro u
        dsimp only
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_sinc_primitive_le hM T u) (norm_nonneg _)
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun u : ℝ ↦ ‖deriv f u‖) volume x
  · have hzero : 𝓕 f = 0 := by
      ext w
      apply integral_undef
      exact fun h ↦ hI ((Real.fourierIntegral_convergent_iff w).mp h)
    simpa only [hzero, Pi.zero_apply, smul_zero, intervalIntegral.integral_zero, norm_zero] using
      mul_nonneg hC (integral_nonneg fun u ↦ norm_nonneg (deriv f u))
