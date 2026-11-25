/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Edge integrals of functions with Mellin cutoff decay

The Mellin transform `𝓜χ_ε` of a smoothed cutoff of a `C¹` bump decays like
`|s|⁻¹ (1 + ε|s|)⁻¹` on vertical strips to the right of `0`, uniformly in `0 < ε ≤ 1`
(`TauCeti.exists_norm_mellin_smoothCutoff_le`). Multiplying it by a function bounded by `M` and by
`xˢ` gives a function `f` with `‖f s‖ ≤ K x^{Re s} / (|s| (1 + ε|s|))`, `K = CM`: this is the
integrand of the inverse Mellin integral of a smoothed sum, after its line of integration has been
moved into a region where the Dirichlet series is bounded. The three edges of the U-shaped contour
of `TauCeti.Contour.integral_vertical_eq_uShaped_symm_add_two_pi_mul_sum_residue` are then
estimated as follows, for `ε > 0` and `T > 0`:

* the two tails `|t| > T` of the vertical line `Re s = σ` contribute at most `2K / (εT)` when
  `‖f(σ + it)‖ ≤ K / (|s| (1 + ε|s|))`;
* the left edge `Re s = σ > 0`, `|t| ≤ T`, contributes at most `4K log(1 + T/σ)` when
  `‖f(σ + it)‖ ≤ K / |s|`: the decay `|s|⁻¹` alone gives the logarithm, without the factor `ε⁻¹`;
* a horizontal edge `Im s = T ≠ 0`, `σ₁ ≤ Re s ≤ σ₂`, contributes at most
  `(σ₂ - σ₁) K x^{σ₂} / (εT²)` for `x ≥ 1` when `‖f(σ + iT)‖ ≤ K x^σ / (|s| (1 + ε|s|))`.

## Main results

* `TauCeti.norm_integral_vertical_tail_le`: the tails of a vertical line.
* `TauCeti.norm_intervalIntegral_vertical_le`: a symmetric segment of a vertical line.
* `TauCeti.norm_intervalIntegral_horizontal_le`: a horizontal segment.

## References

* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd* blueprint, §4.6 (the bounds of the
  integrals `I₁`–`I₉` in the proof of the medium-strength prime number theorem),
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>. The formalization in the Tau Ceti
  fork <https://github.com/TauCetiProject/PrimeNumberTheoremAnd>, file
  `PrimeNumberTheoremAnd/MediumPNT.lean` at revision `df0ccba` (`I1Bound`, `I2GenBound`,
  `I3GenBound`, `I5Bound`), proves these bounds for the integrand `-ζ'/ζ(s) 𝓜χ_ε(s) Xˢ`; the
  statements here isolate the estimates of the edge integrals from the bounds on the integrand.
-/

public section

open Set MeasureTheory Complex
open scoped Interval

namespace TauCeti

/-- The imaginary part of `σ + tI` is at most its norm. -/
private lemma abs_le_norm_ofReal_add_mul_I (σ t : ℝ) : |t| ≤ ‖(σ : ℂ) + t * I‖ := by
  simpa using abs_im_le_norm ((σ : ℂ) + t * I)

/-- If `|t| ≤ ‖z‖` and `ε ≥ 0` then `εt² ≤ ‖z‖ (1 + ε‖z‖)`. -/
private lemma mul_sq_le_norm_mul_one_add {ε t : ℝ} {z : ℂ} (hε : 0 ≤ ε) (ht : |t| ≤ ‖z‖) :
    ε * t ^ 2 ≤ ‖z‖ * (1 + ε * ‖z‖) := by
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) ht 2) hε
  rw [sq_abs] at h
  nlinarith [norm_nonneg z]

/-- **The tails of a vertical line.** If `ε > 0`, `T > 0` and
`‖f(σ + it)‖ ≤ K / (|s| (1 + ε|s|))` at `s = σ + it` for `|t| > T`, then the integral of
`t ↦ f(σ + it)` over `|t| > T` has norm at most `2K / (εT)`. -/
theorem norm_integral_vertical_tail_le {f : ℂ → ℂ} {σ K ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hf : ∀ t : ℝ, T < |t| →
      ‖f (σ + t * I)‖ ≤ K / (‖(σ : ℂ) + t * I‖ * (1 + ε * ‖(σ : ℂ) + t * I‖))) :
    ‖∫ t in {t : ℝ | T < |t|}, f (σ + t * I)‖ ≤ 2 * K / (ε * T) := by
  have hS : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hden {t : ℝ} (ht : T < |t|) : 0 < ε * t ^ 2 := by
    have : t ≠ 0 := abs_pos.mp (hT.trans ht)
    positivity
  have hK : 0 ≤ K := by
    have ht : T < |T + 1| := by rw [abs_of_pos (by linarith)]; linarith
    have hd := (hden ht).trans_le
      (mul_sq_le_norm_mul_one_add hε.le (abs_le_norm_ofReal_add_mul_I σ (T + 1)))
    simpa using (le_div_iff₀ hd).1 ((norm_nonneg _).trans (hf _ ht))
  have hint : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) {t : ℝ | T < |t|} :=
    Integrable.of_integral_ne_zero <| by
      rw [integral_lt_abs_inv_sq hT.le]
      exact div_ne_zero two_ne_zero hT.ne'
  calc ‖∫ t in {t : ℝ | T < |t|}, f (σ + t * I)‖
      ≤ ∫ t in {t : ℝ | T < |t|}, K / ε * (t ^ 2)⁻¹ := by
        refine norm_integral_le_of_norm_le (hint.const_mul _)
          (ae_restrict_of_forall_mem hS fun t (ht : T < |t|) ↦ (hf t ht).trans ?_)
        refine (div_le_div_of_nonneg_left hK (hden ht)
          (mul_sq_le_norm_mul_one_add hε.le (abs_le_norm_ofReal_add_mul_I σ t))).trans_eq ?_
        ring
    _ = 2 * K / (ε * T) := by
        rw [integral_const_mul, integral_lt_abs_inv_sq hT.le]
        field_simp

/-- **A symmetric segment of a vertical line.** If `σ > 0`, `T ≥ 0` and
`‖f(σ + it)‖ ≤ K / |σ + it|` for `|t| ≤ T`, then the integral of `t ↦ f(σ + it)` over `[-T, T]`
has norm at most `4K log(1 + T/σ)`. -/
theorem norm_intervalIntegral_vertical_le {f : ℂ → ℂ} {σ K T : ℝ} (hσ : 0 < σ) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc (-T) T, ‖f (σ + t * I)‖ ≤ K / ‖(σ : ℂ) + t * I‖) :
    ‖∫ t in (-T)..T, f (σ + t * I)‖ ≤ 4 * K * Real.log (1 + T / σ) := by
  have hK : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hf 0 ⟨by linarith, hT⟩)
    have h0 : ‖(σ : ℂ) + ((0 : ℝ) : ℂ) * I‖ = σ := by simp [abs_of_pos hσ]
    rw [h0] at h
    simpa using (le_div_iff₀ hσ).1 h
  have hc : Continuous fun t : ℝ ↦ (σ + |t|)⁻¹ :=
    (continuous_const.add continuous_abs).inv₀ fun t ↦
      (add_pos_of_pos_of_nonneg hσ (abs_nonneg t)).ne'
  calc ‖∫ t in (-T)..T, f (σ + t * I)‖ ≤ ∫ t in (-T)..T, 2 * K * (σ + |t|)⁻¹ := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
          (Filter.Eventually.of_forall fun t ht ↦ (hf t (Ioc_subset_Icc_self ht)).trans ?_)
          ((hc.const_mul _).intervalIntegrable _ _)
        have hre : σ ≤ ‖(σ : ℂ) + t * I‖ := by
          simpa [abs_of_pos hσ] using abs_re_le_norm ((σ : ℂ) + t * I)
        have hpos : 0 < (σ + |t|) / 2 := by positivity
        refine (div_le_div_of_nonneg_left hK hpos
          (by linarith [abs_le_norm_ofReal_add_mul_I σ t])).trans_eq ?_
        field_simp
    _ = 4 * K * Real.log (1 + T / σ) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_add_abs hσ hT]
        ring

/-- **A horizontal segment.** If `σ₁ ≤ σ₂`, `T ≠ 0`, `ε > 0`, `x ≥ 1` and
`‖f(σ + iT)‖ ≤ K x^σ / (|s| (1 + ε|s|))` at `s = σ + iT` for `σ₁ ≤ σ ≤ σ₂`, then the integral of
`σ ↦ f(σ + iT)` over `[σ₁, σ₂]` has norm at most `(σ₂ - σ₁) K x^{σ₂} / (εT²)`. -/
theorem norm_intervalIntegral_horizontal_le {f : ℂ → ℂ} {σ₁ σ₂ T K ε x : ℝ} (hσ : σ₁ ≤ σ₂)
    (hT : T ≠ 0) (hε : 0 < ε) (hx : 1 ≤ x)
    (hf : ∀ σ ∈ Icc σ₁ σ₂, ‖f (σ + T * I)‖ ≤
      K * x ^ σ / (‖(σ : ℂ) + T * I‖ * (1 + ε * ‖(σ : ℂ) + T * I‖))) :
    ‖∫ σ in σ₁..σ₂, f (σ + T * I)‖ ≤ (σ₂ - σ₁) * K * x ^ σ₂ / (ε * T ^ 2) := by
  have hden : 0 < ε * T ^ 2 := by positivity
  have hle (σ : ℝ) := mul_sq_le_norm_mul_one_add hε.le (abs_le_norm_ofReal_add_mul_I σ T)
  have hK : 0 ≤ K := by
    have h := (le_div_iff₀ (hden.trans_le (hle σ₁))).1
      ((norm_nonneg _).trans (hf σ₁ ⟨le_rfl, hσ⟩))
    exact nonneg_of_mul_nonneg_left (by simpa using h) (by positivity)
  have hbound : ∀ σ ∈ Ι σ₁ σ₂, ‖f (σ + T * I)‖ ≤ K * x ^ σ₂ / (ε * T ^ 2) := by
    intro σ hσ'
    rw [uIoc_of_le hσ] at hσ'
    refine (hf σ (Ioc_subset_Icc_self hσ')).trans (div_le_div₀ (by positivity) ?_ hden (hle σ))
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hσ'.2) hK
  calc ‖∫ σ in σ₁..σ₂, f (σ + T * I)‖ ≤ K * x ^ σ₂ / (ε * T ^ 2) * |σ₂ - σ₁| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = (σ₂ - σ₁) * K * x ^ σ₂ / (ε * T ^ 2) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hσ)]
        ring

end TauCeti
