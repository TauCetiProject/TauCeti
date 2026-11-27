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
integrable on `s`, where `f_s` is the average of `f` over `s`. -/
theorem setAverage_norm_sub_setAverage_rpow_le (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    {γ : ℝ} (hγ : 1 ≤ γ) (c : F) (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := by
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  have hγ0 : 0 ≤ γ := zero_le_one.trans hγ
  set K := ⨍ x in s, ‖f x - c‖ ^ γ ∂μ
  have hic : IntegrableOn (fun x ↦ f x - c) s μ := hf.sub (integrableOn_const hs)
  -- By Jensen's inequality, the deviation `‖f_s - c‖` of the average satisfies
  -- `‖f_s - c‖^γ ≤ (⨍_s ‖f - c‖)^γ ≤ K`.
  have hJ : (⨍ x in s, ‖f x - c‖ ∂μ) ^ γ ≤ K :=
    (convexOn_rpow hγ).map_set_average_le
      (continuous_id.rpow_const fun _ ↦ Or.inr hγ0).continuousOn isClosed_Ici h0 hs
      (ae_of_all _ fun x ↦ norm_nonneg (f x - c)) hic.norm hfc
  have heq : (⨍ y in s, f y ∂μ) - c = ⨍ y in s, (f y - c) ∂μ := by
    rw [setAverage_fun_sub hf (integrableOn_const hs), setAverage_const h0 hs]
  set m := ⨍ y in s, f y ∂μ
  have hB : ‖m - c‖ ^ γ ≤ K := by
    refine (Real.rpow_le_rpow (norm_nonneg _) ?_ hγ0).trans hJ
    rw [heq, setAverage_eq, setAverage_eq, norm_smul, Real.norm_of_nonneg (by positivity),
      smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  -- Pointwise, `‖f - f_s‖^γ ≤ (‖f - c‖ + ‖f_s - c‖)^γ ≤ 2^(γ - 1) (‖f - c‖^γ + ‖f_s - c‖^γ)`
  -- by the convexity of `t ↦ t^γ`.
  have hpt : ∀ x, ‖f x - m‖ ^ γ ≤ 2 ^ γ / 2 * (‖f x - c‖ ^ γ + ‖m - c‖ ^ γ) := fun x ↦ by
    have hAB : ‖f x - m‖ ≤ ‖f x - c‖ + ‖m - c‖ := by
      simpa using norm_sub_le (f x - c) (m - c)
    have hconv := (convexOn_rpow hγ).2 (Set.mem_Ici.2 (norm_nonneg (f x - c)))
      (Set.mem_Ici.2 (norm_nonneg (m - c))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hconv
    calc ‖f x - m‖ ^ γ ≤ (‖f x - c‖ + ‖m - c‖) ^ γ :=
          Real.rpow_le_rpow (norm_nonneg _) hAB hγ0
      _ = 2 ^ γ * (1 / 2 * ‖f x - c‖ + 1 / 2 * ‖m - c‖) ^ γ := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
          ring_nf
      _ ≤ 2 ^ γ * (1 / 2 * ‖f x - c‖ ^ γ + 1 / 2 * ‖m - c‖ ^ γ) := by gcongr
      _ = _ := by ring
  calc ⨍ x in s, ‖f x - m‖ ^ γ ∂μ
      ≤ ⨍ x in s, 2 ^ γ / 2 * (‖f x - c‖ ^ γ + ‖m - c‖ ^ γ) ∂μ := by
        rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul]
        refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (ae_of_all _ fun _ ↦ by positivity)
          ((hfc.add (integrableOn_const hs)).const_mul _) (ae_of_all _ hpt)) (by positivity)
    _ = 2 ^ γ / 2 * (K + ‖m - c‖ ^ γ) := by
        rw [average_const_mul, setAverage_fun_add hfc (integrableOn_const hs),
          setAverage_const h0 hs]
    _ ≤ 2 ^ γ / 2 * (K + K) := by gcongr
    _ = 2 ^ γ * K := by ring

end TauCeti
