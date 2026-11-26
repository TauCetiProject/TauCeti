/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.SineIntegral

import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
import TauCeti.Analysis.Fourier.RiemannLebesgue
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The sinc kernel for symmetric Fourier inversion

The finite-height kernel has a bounded primitive given by `Real.integral_sin_mul_div_eq_sub`.
The uniform bound uses `Real.abs_integral_sin_mul_div_le`.
Its mass on a fixed positive half-window tends to one half by
`TauCeti.Contour.tendsto_integral_sinc_atTop`. The symmetric window uses
`intervalIntegral.integral_eq_two_smul_of_even`. The tail estimate uses
`MeasureTheory.Integrable.tendsto_integral_sin_smul_atTop`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, §5.1.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti

/-- The real convolution kernel for truncating the inverse Fourier integral to `[-T, T]`. -/
noncomputable def sincKernel (T u : ℝ) : ℝ :=
  2 * T * Real.sinc (2 * Real.pi * T * u)

/-- The Fourier sinc kernel in terms of Mathlib’s sinc function, which is `sin x / x` off zero. -/
theorem sincKernel_apply (T u : ℝ) :
    sincKernel T u = 2 * T * Real.sinc (2 * Real.pi * T * u) := (rfl)

/-- The sinc kernel is even in the spatial variable. -/
@[simp] theorem sincKernel_neg (T u : ℝ) : sincKernel T (-u) = sincKernel T u := by
  simp [sincKernel, mul_neg, Real.sinc_neg]

/-- At the origin the sinc kernel is twice the truncation height. -/
@[simp] theorem sincKernel_zero_right (T : ℝ) : sincKernel T 0 = 2 * T := by
  simp [sincKernel]

/-- At zero truncation height the sinc kernel vanishes. -/
@[simp] theorem sincKernel_zero_left (u : ℝ) : sincKernel 0 u = 0 := by
  simp [sincKernel]

/-- For a fixed truncation height, the sinc kernel is continuous in the spatial variable. -/
@[fun_prop]
theorem continuous_sincKernel (T : ℝ) : Continuous (sincKernel T) := by
  unfold sincKernel
  fun_prop

/-- Off the origin, the Fourier sinc kernel is the normalized sine quotient. -/
theorem sincKernel_eq_sin_div {u : ℝ} (hu : u ≠ 0) (T : ℝ) :
    sincKernel T u = Real.sin (2 * Real.pi * T * u) / (Real.pi * u) := by
  by_cases hT : T = 0
  · simp [sincKernel, hT]
  · rw [sincKernel, Real.sinc_of_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hT) hu)]
    field_simp

/-- The sinc kernel and the normalized sine quotient agree almost everywhere for volume. -/
theorem sincKernel_ae_eq_sin_div (T : ℝ) :
    sincKernel T =ᵐ[volume] fun u ↦ Real.sin (2 * Real.pi * T * u) / (Real.pi * u) := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
  exact sincKernel_eq_sin_div (by simpa using hu) T

/-- The norm of the sinc kernel is bounded by twice the absolute truncation height. -/
theorem norm_sincKernel_le (T u : ℝ) : ‖sincKernel T u‖ ≤ 2 * |T| := by
  rw [sincKernel, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

end TauCeti

/-- Multiplication by the sinc kernel preserves integrability for any measure. -/
theorem MeasureTheory.Integrable.sincKernel_smul
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} {f : ℝ → E} (hf : Integrable f μ) (T : ℝ) :
    Integrable (fun u ↦ TauCeti.sincKernel T u • f u) μ := by
  have hn : Integrable (fun u ↦ ‖f u‖) μ :=
    hf.mono_eNorm hf.aestronglyMeasurable.norm (.of_forall fun _ ↦ by simp)
  refine (hn.const_mul (2 * |T|)).mono_eNorm
    ((TauCeti.continuous_sincKernel T).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (.of_forall fun u ↦ ?_)
  have hnonneg : 0 ≤ 2 * |T| * ‖f u‖ := by positivity
  rw [eNorm_le_iff_norm_le, norm_smul, Real.norm_of_nonneg hnonneg]
  exact mul_le_mul_of_nonneg_right (TauCeti.norm_sincKernel_le T u) (norm_nonneg _)

namespace TauCeti

/-- The integral of the sinc kernel equals the normalized Dirichlet integral. -/
theorem intervalIntegral_sincKernel_eq_sin_div (T a b : ℝ) :
    ∫ u in a..b, sincKernel T u =
      Real.pi⁻¹ * ∫ u in a..b, Real.sin (2 * Real.pi * T * u) / u := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [sincKernel_ae_eq_sin_div T] with u hu _
  rw [hu]
  ring

/-- The interval integral of the sinc kernel is the normalized difference of sine integrals. -/
theorem intervalIntegral_sincKernel (T a b : ℝ) :
    ∫ u in a..b, sincKernel T u = Real.pi⁻¹ *
      (Real.sineIntegral (2 * Real.pi * T * b) - Real.sineIntegral (2 * Real.pi * T * a)) := by
  rw [intervalIntegral_sincKernel_eq_sin_div, Real.integral_sin_mul_div_eq_sub]

/-- The sinc kernel has a uniform integral bound over every oriented interval. -/
theorem norm_intervalIntegral_sincKernel_le (T a b : ℝ) :
    ‖∫ u in a..b, sincKernel T u‖ ≤ 2 * Real.sineIntegral Real.pi / Real.pi := by
  rw [intervalIntegral_sincKernel_eq_sin_div, norm_mul, Real.norm_of_nonneg (by positivity)]
  simpa only [Real.norm_eq_abs, div_eq_inv_mul] using
    mul_le_mul_of_nonneg_left (Real.abs_integral_sin_mul_div_le (2 * Real.pi * T) a b)
      (inv_nonneg.mpr Real.pi_pos.le)

/-- The mass of the sinc kernel on a fixed positive half-window tends to one half
(Montgomery and Vaughan, *Multiplicative Number Theory I*, §5.1). -/
theorem tendsto_intervalIntegral_sincKernel {d : ℝ} (hd : 0 < d) :
    Tendsto (fun T : ℝ ↦ ∫ u in 0..d, sincKernel T u) atTop (𝓝 (1 / 2)) := by
  have hscale : 0 < 2 * Real.pi * d := by positivity
  have hSi : Tendsto Real.sineIntegral atTop (𝓝 (Real.pi / 2)) := by
    simpa only [Real.integral_sinc_eq_sub, Real.sineIntegral_zero, sub_zero] using
      Contour.tendsto_integral_sinc_atTop
  have h := (hSi.comp (tendsto_id.const_mul_atTop hscale)).const_mul Real.pi⁻¹
  convert h using 1
  · ext T
    rw [intervalIntegral_sincKernel, mul_zero, Real.sineIntegral_zero, sub_zero]
    dsimp
    ring_nf
  · field_simp [Real.pi_ne_zero]

/-- The sinc kernel has limiting mass one on each fixed symmetric window of positive radius. -/
theorem tendsto_intervalIntegral_sincKernel_symmetric {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ ↦ ∫ u in -R..R, sincKernel T u) atTop (𝓝 1) := by
  have hmass : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have H := (tendsto_intervalIntegral_sincKernel hR).const_mul 2
  rw [hmass] at H
  refine H.congr fun T ↦ ?_
  simpa only [smul_eq_mul] using
    (intervalIntegral.integral_eq_two_smul_of_even (sincKernel_neg T) R).symm

/-- The integral of the sinc kernel against an integrable function on a right tail tends to
zero when the tail starts at a positive distance from the origin. -/
theorem tendsto_setIntegral_sincKernel_smul_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℝ → E} {d : ℝ} (hd : 0 < d) (hf : IntegrableOn f (Ioi d)) :
    Tendsto (fun T : ℝ ↦ ∫ u in Ioi d, sincKernel T u • f u) atTop (𝓝 0) := by
  have hq : IntegrableOn (fun u ↦ ((Real.pi * u)⁻¹ : ℝ) • f u) (Ioi d) := by
    refine hf.bdd_smul (φ := fun u ↦ (Real.pi * u)⁻¹) (Real.pi * d)⁻¹ (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu₀ : 0 < u := hd.trans hu
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (Real.pi * u)⁻¹)]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hu.le Real.pi_pos.le)
  have H := ((integrable_indicator_iff measurableSet_Ioi).2 hq).tendsto_integral_sin_smul_atTop
  refine H.congr (fun T ↦ ?_)
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioi d
  · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, Complex.coe_smul, smul_smul,
      sincKernel_eq_sin_div (hd.trans hu).ne', div_eq_mul_inv]
  · simp [hu]

end TauCeti
