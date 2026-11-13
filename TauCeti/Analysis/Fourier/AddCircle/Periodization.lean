/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Periodized kernels on the circle

For a smooth compactly supported symbol `η : ℝ → ℂ` and a scale `R > 0`, the trigonometric
polynomial `t ↦ ∑ n, η (n / R) e_n(t)` on the circle `UnitAddCircle = ℝ / ℤ` has only the
frequencies `|n| ≤ M R` when `η` vanishes outside `[-M, M]`
(`TauCeti.tsum_mul_fourier_eq_sum`). By Poisson summation (`SchwartzMap.tsum_eq_tsum_fourier`) it
is the periodization `x ↦ ∑ ℓ, G (x + ℓ)` of the kernel `G = 𝓕⁻ (η (· / R))` on `ℝ`, a dilate of
`𝓕⁻ η`. Hence its `L¹` norm on the circle is at most `∫ ‖G‖ = ∫ ‖𝓕⁻ η‖`, whatever the scale `R`
(`TauCeti.integral_norm_tsum_mul_fourier_le`). This is the bound that makes kernels of de la Vallée
Poussin type uniformly integrable.

## Main declarations

* `TauCeti.tsum_mul_fourier_eq_sum`: the periodized kernel is a trigonometric polynomial.
* `TauCeti.continuous_tsum_mul_fourier`: the periodized kernel is continuous.
* `TauCeti.integral_norm_tsum_mul_fourier_le`: the `L¹` norm on the circle of the periodized
  kernel `t ↦ ∑ n, η (n / R) e_n(t)` is at most `∫ ‖𝓕⁻ η‖`, uniformly in `R`.
-/

public section

open MeasureTheory Set FourierTransform
open scoped ContDiff

namespace TauCeti

/-- A compactly supported function vanishes outside some interval `[-M, M]`. -/
private theorem exists_forall_lt_abs_eq_zero {η : ℝ → ℂ}
    (hc : HasCompactSupport η) : ∃ M : ℝ, ∀ ξ, M < |ξ| → η ξ = 0 := by
  obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, fun ξ hξ ↦ image_eq_zero_of_notMem_tsupport fun h ↦ ?_⟩
  have := hM h
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith

/-- If `η` vanishes outside `[-M, M]` and `R > 0`, the periodized kernel
`t ↦ ∑ n, η (n / R) e_n(t)` is the trigonometric polynomial with frequencies `|n| ≤ ⌈M R⌉`. -/
theorem tsum_mul_fourier_eq_sum {η : ℝ → ℂ} {M R : ℝ} (hR : 0 < R)
    (hη : ∀ ξ, M < |ξ| → η ξ = 0) (t : UnitAddCircle) :
    ∑' n : ℤ, η (n / R) * fourier n t =
      ∑ n ∈ Finset.Icc (-⌈M * R⌉) ⌈M * R⌉, η (n / R) * fourier n t := by
  refine tsum_eq_sum fun n hn ↦ ?_
  rw [Finset.mem_Icc, ← abs_le, not_le] at hn
  have hn' : M * R < |(n : ℝ)| :=
    (Int.le_ceil _).trans_lt (by exact_mod_cast hn)
  rw [hη _ (by rwa [abs_div, abs_of_pos hR, lt_div_iff₀ hR]), zero_mul]

/-- For compactly supported `η` and `R > 0`, the periodized kernel `t ↦ ∑ n, η (n / R) e_n(t)` is
continuous. -/
theorem continuous_tsum_mul_fourier {η : ℝ → ℂ} (hc : HasCompactSupport η) {R : ℝ}
    (hR : 0 < R) : Continuous fun t : UnitAddCircle ↦ ∑' n : ℤ, η (n / R) * fourier n t := by
  obtain ⟨M, hM⟩ := exists_forall_lt_abs_eq_zero hc
  simp only [tsum_mul_fourier_eq_sum hR hM]
  fun_prop

/-- **The `L¹` norm of a periodized kernel.** For a smooth compactly supported `η : ℝ → ℂ` and
`R > 0`, the trigonometric polynomial `t ↦ ∑ n, η (n / R) e_n(t)` on the circle, the periodization
of the kernel `𝓕⁻ (η (· / R))` on `ℝ`, has `L¹` norm at most `∫ ‖𝓕⁻ η‖`, independently of `R`. -/
theorem integral_norm_tsum_mul_fourier_le {η : ℝ → ℂ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) {R : ℝ} (hR : 0 < R) :
    ∫ t : UnitAddCircle, ‖∑' n : ℤ, η (n / R) * fourier n t‖ ≤ ∫ y, ‖𝓕⁻ η y‖ := by
  -- The symbol `η (· / R)` as a Schwartz function, and its kernel `G`.
  have hcR : HasCompactSupport fun ξ : ℝ ↦ η (R⁻¹ • ξ) := hc.comp_smul (inv_ne_zero hR.ne')
  have hsR : ContDiff ℝ ∞ fun ξ : ℝ ↦ η (R⁻¹ • ξ) := hη.comp (contDiff_const_smul _)
  set S : SchwartzMap ℝ ℂ := hcR.toSchwartzMap hsR
  set G : SchwartzMap ℝ ℂ := 𝓕⁻ S
  have hG : (G : ℝ → ℂ) = 𝓕⁻ fun ξ : ℝ ↦ η (R⁻¹ • ξ) := by
    rw [SchwartzMap.fourierInv_coe]
    exact congrArg 𝓕⁻ (funext (HasCompactSupport.toSchwartzMap_toFun hcR hsR))
  have hFG (n : ℤ) : 𝓕 G (n : ℝ) = η (n / R) := by
    simp only [G, FourierTransform.fourier_fourierInv_eq, S, HasCompactSupport.toSchwartzMap_toFun,
      smul_eq_mul, div_eq_inv_mul]
  -- Poisson summation: the kernel is the periodization of `G`.
  have hpoisson (x : ℝ) : ∑' n : ℤ, η (n / R) * fourier n (x : UnitAddCircle) =
      ∑' ℓ : ℤ, G (x + ℓ) := by
    rw [SchwartzMap.tsum_eq_tsum_fourier G x]
    simp only [hFG]
  have hGint : Integrable (G : ℝ → ℂ) := G.integrable
  have hsum := hGint.norm.hasSum_intervalIntegral_comp_add_int
  have hmeas (ℓ : ℤ) : Measurable fun x : ℝ ↦ ‖G (x + ℓ)‖ₑ :=
    (G.continuous.comp (continuous_id.add continuous_const)).eNorm.measurable
  have hlint : ∫⁻ t : UnitAddCircle, ‖∑' n : ℤ, η (n / R) * fourier n t‖ₑ ≤
      ENNReal.ofReal (∫ y, ‖G y‖) := by
    rw [← UnitAddCircle.lintegral_preimage 0]
    calc ∫⁻ x in Ioc (0 : ℝ) (0 + 1), ‖∑' n : ℤ, η (n / R) * fourier n (x : UnitAddCircle)‖ₑ
        ≤ ∫⁻ x in Ioc (0 : ℝ) (0 + 1), ∑' ℓ : ℤ, ‖G (x + ℓ)‖ₑ :=
          lintegral_mono fun x ↦ (hpoisson x).symm ▸ eNorm_tsum_le_tsum_eNorm
      _ = ∑' ℓ : ℤ, ∫⁻ x in Ioc (0 : ℝ) (0 + 1), ‖G (x + ℓ)‖ₑ :=
          lintegral_tsum fun ℓ ↦ (hmeas ℓ).aemeasurable
      _ = ∑' ℓ : ℤ, ENNReal.ofReal (∫ x in (0 : ℝ)..1, ‖G (x + ℓ)‖) := by
          congr 1 with ℓ
          rw [intervalIntegral.integral_of_le zero_le_one, zero_add,
            ofReal_integral_norm_eq_lintegral_eNorm]
          exact ((G.continuous.comp (continuous_id.add continuous_const)).integrableOn_Icc).mono_set
            Ioc_subset_Icc_self
      _ = ENNReal.ofReal (∫ y, ‖G y‖) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun ℓ ↦ intervalIntegral.integral_nonneg
            zero_le_one fun x _ ↦ norm_nonneg _) hsum.summable, hsum.tsum_eq]
  calc ∫ t : UnitAddCircle, ‖∑' n : ℤ, η (n / R) * fourier n t‖
      ≤ ∫ y, ‖G y‖ := by
        rw [integral_norm_eq_lintegral_eNorm
          (continuous_tsum_mul_fourier hc hR).aestronglyMeasurable]
        exact ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun _ ↦ norm_nonneg _) hlint
    _ = ∫ y, ‖𝓕⁻ η y‖ := by
        rw [hG]
        exact integral_norm_fourierInv_comp_smul η (inv_ne_zero hR.ne')

end TauCeti
