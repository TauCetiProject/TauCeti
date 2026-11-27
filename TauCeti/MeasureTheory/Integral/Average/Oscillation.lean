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
`TauCeti.setIntegral_norm_sub_setAverage_sq_le`. For every real exponent `γ ≥ 1` the averaged
form `⨍_s ‖f - f_s‖^γ ≤ 2^γ ⨍_s ‖f - c‖^γ` holds as well; it is the form in which mean
oscillations in `L^γ` enter the sharp function method.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul`: `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.
* `TauCeti.setAverage_norm_sub_setAverage_rpow_le`: `⨍_s ‖f - f_s‖^γ ≤ 2^γ ⨍_s ‖f - c‖^γ` for
  `γ ≥ 1`.
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

/-- **The `L^γ` mean oscillation about the average.** On a set `s` of finite measure and for
`γ ≥ 1`, `⨍_s ‖f - f_s‖^γ ≤ 2^γ ⨍_s ‖f - c‖^γ` for every constant `c` for which `‖f - c‖^γ` is
integrable on `s`, where `f_s` is the average of `f` over `s`. This is
`TauCeti.eLpNorm_sub_setAverage_le` at `p = γ`, raised to the power `γ`. -/
theorem setAverage_norm_sub_setAverage_rpow_le (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    {γ : ℝ} (hγ : 1 ≤ γ) (c : F) (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ0
  -- Raise the `Lᵖ` comparison `TauCeti.eLpNorm_sub_setAverage_le`, `p = γ`, to the power `γ`.
  have h := eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs (p := ENNReal.ofReal γ)
    (by simpa using hγ) c
  have hic : MemLp (fun x ↦ f x - c) (ENNReal.ofReal γ) (μ.restrict s) :=
    (integrable_norm_rpow_iff (hf.sub (integrableOn_const hs)).aestronglyMeasurable hp0
      ENNReal.ofReal_ne_top).1 (by rwa [ENNReal.toReal_ofReal hγ0.le])
  have hia : MemLp (fun x ↦ f x - ⨍ y in s, f y ∂μ) (ENNReal.ofReal γ) (μ.restrict s) :=
    h.trans_lt (ENNReal.mul_lt_top (by simp) hic)
  rw [hia.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    hic.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hγ0.le,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have h' := Real.rpow_le_rpow (by positivity) h hγ0.le
  rw [Real.mul_rpow zero_le_two (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hγ0.ne', Real.rpow_one,
    Real.rpow_one] at h'
  generalize ⨍ y in s, f y ∂μ = m at h'
  rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left h' (by positivity)

end TauCeti
