/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average

/-!
# The mean oscillation about the average

On a set `s` of finite measure, the `L¹` deviation of an integrable `f` from its average
`f_s = ⨍_s f` is at most twice its deviation from any constant `c`:

`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.

This is the Bochner-integral form, at `p = 1`, of the `Lᵖ` comparison
`TauCeti.eLpNorm_sub_setAverage_le`; its `L²` analogue, with factor `4`, is
`TauCeti.setIntegral_norm_sub_setAverage_sq_le`. For every exponent `γ ≥ 1` the same comparison
holds for the means of the `γ`-th powers, with factor `2 ^ γ`:

`⨍_s ‖f - f_s‖ ^ γ ≤ 2 ^ γ ⨍_s ‖f - c‖ ^ γ`,

the `γ`-th power of the `Lᵖ` comparison at `p = γ`. Jensen's inequality
`(⨍_s ‖g‖) ^ γ ≤ ⨍_s ‖g‖ ^ γ` is recorded alongside.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul`: `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.
* `TauCeti.rpow_setAverage_norm_le_setAverage_norm_rpow`: Jensen's inequality
  `(⨍_s ‖g‖) ^ γ ≤ ⨍_s ‖g‖ ^ γ` for `γ ≥ 1`.
* `TauCeti.setAverage_norm_sub_setAverage_rpow_le`: `⨍_s ‖f - f_s‖ ^ γ ≤ 2 ^ γ ⨍_s ‖f - c‖ ^ γ`
  for `γ ≥ 1`.
-/

public section

namespace TauCeti

open MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {s : Set X}

/-- **The `L¹` mean oscillation about the average.** On a set `s` of finite measure,
`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖` for every constant `c`, where `f_s` is the average of `f` over
`s`. -/
theorem setIntegral_norm_sub_setAverage_le_two_mul (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    (c : F) : ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ∂μ ≤ 2 * ∫ x in s, ‖f x - c‖ ∂μ := by
  have h := eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs le_rfl c
  have hia : IntegrableOn (fun x ↦ f x - ⨍ y in s, f y ∂μ) s μ := hf.sub (integrableOn_const hs)
  have hic : IntegrableOn (fun x ↦ f x - c) s μ := hf.sub (integrableOn_const hs)
  rw [eLpNorm_one_eq_lintegral_eNorm hia.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm hic.aestronglyMeasurable] at h
  rw [integral_norm_eq_lintegral_eNorm hia.aestronglyMeasurable,
    integral_norm_eq_lintegral_eNorm hic.aestronglyMeasurable, ← ENNReal.toReal_ofNat,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hic.2.ne) h

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- **Jensen's inequality for a power of a mean.** For `γ ≥ 1`, if `‖g‖ ^ γ` is integrable on
`s`, then `(⨍_s ‖g‖) ^ γ ≤ ⨍_s ‖g‖ ^ γ`. If `μ s` is `0` or `∞`, both averages are `0`. -/
theorem rpow_setAverage_norm_le_setAverage_norm_rpow {g : X → F} {γ : ℝ} (hγ : 1 ≤ γ)
    (hg : IntegrableOn (fun x ↦ ‖g x‖ ^ γ) s μ) :
    (⨍ x in s, ‖g x‖ ∂μ) ^ γ ≤ ⨍ x in s, ‖g x‖ ^ γ ∂μ := by
  have hγ0 : 0 ≤ γ := zero_le_one.trans hγ
  have ha : 0 ≤ ⨍ x in s, ‖g x‖ ∂μ := average_nonneg fun _ ↦ norm_nonneg _
  have h1 := ENNReal.rpow_le_rpow (enorm_setAverage_le_setLAverage μ (fun x ↦ ‖g x‖) s) hγ0
  simp only [eNorm_norm, Real.eNorm_of_nonneg ha] at h1
  have h := h1.trans ((rpow_laverage_le_laverage_rpow (μ := μ.restrict s)
    (u := fun x ↦ ‖g x‖ₑ) hγ).trans_eq (ofReal_setAverage_norm_rpow hγ0 hg).symm)
  rw [ENNReal.ofReal_rpow_of_nonneg ha hγ0] at h
  exact (ENNReal.ofReal_le_ofReal_iff (average_nonneg fun _ ↦ by positivity)).1 h

/-- **The `L^γ` mean oscillation about the average.** For `γ ≥ 1`,
`⨍_s ‖f - f_s‖ ^ γ ≤ 2 ^ γ ⨍_s ‖f - c‖ ^ γ` for every constant `c` with `‖f - c‖ ^ γ`
integrable on `s`, where `f_s` is the average of `f` over `s`. This is the `γ`-th power of the
`Lᵖ` comparison `TauCeti.eLpNorm_sub_setAverage_le` at `p = γ`, divided by `μ s`. -/
theorem setAverage_norm_sub_setAverage_rpow_le (hf : IntegrableOn f s μ) {γ : ℝ} (hγ : 1 ≤ γ)
    {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hR : 0 ≤ 2 ^ γ * ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := by
    have : 0 ≤ ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := average_nonneg fun _ ↦ by positivity
    positivity
  -- On a set of infinite measure every average vanishes, and so does the average of a
  -- non-integrable function.
  rcases eq_or_ne (μ s) ⊤ with hs | hs
  · simp [setAverage_eq, measureReal_def, hs]
  by_cases hi : IntegrableOn (fun x ↦ ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ) s μ
  swap
  · rwa [setAverage_eq, integral_undef hi, smul_zero]
  have h := ENNReal.rpow_le_rpow (eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs
    (p := ENNReal.ofReal γ) (by simpa using hγ) c) hγ0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hγ0.le,
    eLpNorm_eq_eLpNorm' (by simpa using hγ0) ENNReal.ofReal_ne_top
      (f := fun x ↦ f x - ⨍ y in s, f y ∂μ) (hf.1.sub aestronglyMeasurable_const),
    eLpNorm_eq_eLpNorm' (by simpa using hγ0) ENNReal.ofReal_ne_top
      (f := fun x ↦ f x - c) (hf.1.sub aestronglyMeasurable_const),
    ENNReal.toReal_ofReal hγ0.le, ← lintegral_rpow_eNorm_eq_rpow_eLpNorm' hγ0,
    ← lintegral_rpow_eNorm_eq_rpow_eLpNorm' hγ0] at h
  rw [← ENNReal.ofReal_le_ofReal_iff hR, ENNReal.ofReal_mul (by positivity),
    ofReal_setAverage_norm_rpow hγ0.le hi, ofReal_setAverage_norm_rpow hγ0.le hfc,
    setLAverage_eq, setLAverage_eq, ← ENNReal.ofReal_rpow_of_nonneg zero_le_two hγ0.le,
    ENNReal.ofReal_ofNat, ← mul_div_assoc]
  exact ENNReal.div_le_div_right h _

end TauCeti
