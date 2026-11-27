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

since `‖f_s - c‖ ≤ ⨍_s ‖f - c‖` and Jensen's inequality bounds `(⨍_s ‖f - c‖) ^ γ` by
`⨍_s ‖f - c‖ ^ γ`.

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
integrable on `s`, where `f_s` is the average of `f` over `s`. -/
theorem setAverage_norm_sub_setAverage_rpow_le (hf : IntegrableOn f s μ) {γ : ℝ} (hγ : 1 ≤ γ)
    {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := by
  have hγ0 : 0 ≤ γ := zero_le_one.trans hγ
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  -- On a set of infinite measure every average vanishes.
  rcases eq_or_ne (μ s) ⊤ with hs | hs
  · simp [setAverage_eq, measureReal_def, hs]
  have hm : 0 < μ.real s := ENNReal.toReal_pos h0 hs
  set a := ‖(⨍ y in s, f y ∂μ) - c‖
  set I := ∫ x in s, ‖f x - c‖ ^ γ ∂μ
  -- The average lies within the mean of `‖f - c‖` of `c`, so Jensen's inequality bounds `a ^ γ`
  -- by the mean of `‖f - c‖ ^ γ`, that is `μ s * a ^ γ ≤ I`.
  have ha : a ≤ ⨍ x in s, ‖f x - c‖ ∂μ := by
    simpa [div_self hm.ne'] using norm_setAverage_sub_le_of_subset subset_rfl h0 hs hf c
  have haI : μ.real s * a ^ γ ≤ I := by
    calc μ.real s * a ^ γ ≤ μ.real s * ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := by
          gcongr
          exact (Real.rpow_le_rpow (norm_nonneg _) ha hγ0).trans
            (rpow_setAverage_norm_le_setAverage_norm_rpow hγ hfc)
      _ = I := by rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  -- Pointwise, `‖f x - f_s‖ ^ γ ≤ 2 ^ (γ - 1) (‖f x - c‖ ^ γ + a ^ γ)`.
  have hpt : ∀ x, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ≤ 2 ^ (γ - 1) * (‖f x - c‖ ^ γ + a ^ γ) := by
    intro x
    have htri : ‖f x - ⨍ y in s, f y ∂μ‖ ≤ ‖f x - c‖ + a := by
      calc ‖f x - ⨍ y in s, f y ∂μ‖ = ‖(f x - c) - ((⨍ y in s, f y ∂μ) - c)‖ := by
            congr 1; abel
        _ ≤ ‖f x - c‖ + a := norm_sub_le _ _
    exact (Real.rpow_le_rpow (norm_nonneg _) htri hγ0).trans (by
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ⟨_, norm_nonneg (f x - c)⟩
        ⟨a, norm_nonneg _⟩ hγ)
  have hint : IntegrableOn (fun x ↦ 2 ^ (γ - 1) * (‖f x - c‖ ^ γ + a ^ γ)) s μ :=
    (hfc.add (integrableOn_const hs)).const_mul _
  have hbound : ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * I :=
    calc ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ
        ≤ ∫ x in s, 2 ^ (γ - 1) * (‖f x - c‖ ^ γ + a ^ γ) ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity) hint (ae_of_all _ hpt)
      _ = 2 ^ (γ - 1) * (I + μ.real s * a ^ γ) := by
          rw [integral_const_mul, integral_add hfc (integrableOn_const hs), setIntegral_const,
            smul_eq_mul]
      _ ≤ 2 ^ (γ - 1) * (2 * I) := by gcongr; linarith
      _ = 2 ^ γ * I := by
          rw [← mul_assoc, ← Real.rpow_add_one two_ne_zero, sub_add_cancel]
  calc ⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ
      = (μ.real s)⁻¹ * ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ := by
        rw [setAverage_eq (f := fun x ↦ ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ), smul_eq_mul]
    _ ≤ (μ.real s)⁻¹ * (2 ^ γ * I) := by gcongr
    _ = 2 ^ γ * ⨍ x in s, ‖f x - c‖ ^ γ ∂μ := by
        rw [setAverage_eq (f := fun x ↦ ‖f x - c‖ ^ γ), smul_eq_mul]
        ring

end TauCeti
