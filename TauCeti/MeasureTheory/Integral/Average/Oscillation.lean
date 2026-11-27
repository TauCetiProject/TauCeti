/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The `L¹` mean oscillation about the average

On a set `s` of finite measure, the `L¹` deviation of an integrable `f` from its average
`f_s = ⨍_s f` is at most twice its deviation from any constant `c`:

`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.

This is the Bochner-integral form, at `p = 1`, of the `Lᵖ` comparison
`TauCeti.eLpNorm_sub_setAverage_le`; its `L²` analogue, with factor `4`, is
`TauCeti.setIntegral_norm_sub_setAverage_sq_le`.

The same comparison holds for every power `γ ≥ 1` of the deviation, with factor `2^γ`, and
Jensen's inequality bounds the `γ`-th power of the mean of `‖g‖` by the mean of `‖g‖^γ`.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul`: `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.
* `TauCeti.setIntegral_norm_sub_setAverage_rpow_le`: `∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ` for
  `γ ≥ 1`.
* `TauCeti.setAverage_norm_rpow_le`: `(⨍_s ‖g‖)^γ ≤ ⨍_s ‖g‖^γ` for `γ ≥ 1`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

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

/-- **The `Lᵖ` mean oscillation about the average, in integral form.** On a set `s` of finite
measure, for `γ ≥ 1` and every constant `c` with `‖f - c‖^γ` integrable on `s`,
`∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ`, where `f_s` is the average of `f` over `s`. -/
theorem setIntegral_norm_sub_setAverage_rpow_le (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    {γ : ℝ} (hγ : 1 ≤ γ) {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ∫ x in s, ‖f x - c‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  set p : ℝ≥0∞ := ENNReal.ofReal γ
  have hp0 : p ≠ 0 := by simpa [p] using hγ0
  have hpt : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpγ : p.toReal = γ := ENNReal.toReal_ofReal hγ0.le
  have hmc : MemLp (fun x ↦ f x - c) p (μ.restrict s) :=
    (integrable_norm_rpow_iff (hf.sub (integrableOn_const hs)).aestronglyMeasurable hp0 hpt).1
      (by rwa [hpγ])
  have hma : MemLp (fun x ↦ f x - ⨍ y in s, f y ∂μ) p (μ.restrict s) :=
    (hmc.add (memLp_const (c - ⨍ y in s, f y ∂μ))).ae_eq (ae_of_all _ fun x ↦ by
      simp only [Pi.add_apply]
      abel)
  have h := eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs (ENNReal.one_le_ofReal.2 hγ) c
  rw [hma.eLpNorm_eq_integral_rpow_norm hp0 hpt, hmc.eLpNorm_eq_integral_rpow_norm hp0 hpt, hpγ,
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have hI₁ : 0 ≤ ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ :=
    integral_nonneg fun _ ↦ by positivity
  have hI₂ : 0 ≤ ∫ x in s, ‖f x - c‖ ^ γ ∂μ := integral_nonneg fun _ ↦ by positivity
  calc ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ
      = ((∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ) ^ γ⁻¹) ^ γ := by
        rw [← Real.rpow_mul hI₁, inv_mul_cancel₀ hγ0.ne', Real.rpow_one]
    _ ≤ (2 * (∫ x in s, ‖f x - c‖ ^ γ ∂μ) ^ γ⁻¹) ^ γ := by gcongr
    _ = 2 ^ γ * ∫ x in s, ‖f x - c‖ ^ γ ∂μ := by
        rw [Real.mul_rpow zero_le_two (by positivity), ← Real.rpow_mul hI₂,
          inv_mul_cancel₀ hγ0.ne', Real.rpow_one]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- **Jensen's inequality for the mean of a norm.** For `γ ≥ 1`, if `‖g‖^γ` is integrable on `s`,
then `(⨍_s ‖g‖)^γ ≤ ⨍_s ‖g‖^γ`. -/
theorem setAverage_norm_rpow_le {g : X → F} {γ : ℝ} (hγ : 1 ≤ γ)
    (hgγ : IntegrableOn (fun x ↦ ‖g x‖ ^ γ) s μ) :
    (⨍ x in s, ‖g x‖ ∂μ) ^ γ ≤ ⨍ x in s, ‖g x‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hR : 0 ≤ ⨍ x in s, ‖g x‖ ^ γ ∂μ := average_nonneg fun _ ↦ by positivity
  by_cases hg : IntegrableOn (fun x ↦ ‖g x‖) s μ
  swap
  · rwa [setAverage_eq, integral_undef hg, smul_zero, Real.zero_rpow hγ0.ne']
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0, Real.zero_rpow hγ0.ne']
  rcases eq_or_ne (μ s) ⊤ with ht | ht
  · simp [setAverage_eq, measureReal_def, ht, Real.zero_rpow hγ0.ne']
  exact ConvexOn.map_set_average_le (convexOn_rpow hγ)
    (continuous_id.rpow_const fun _ ↦ Or.inr hγ0.le).continuousOn isClosed_Ici h0 ht
    (ae_of_all _ fun x ↦ norm_nonneg (g x)) hg hgγ

end TauCeti
