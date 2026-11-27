/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average

/-!
# The `L¹` mean oscillation about the average

On a set `s` of finite measure, the `L¹` deviation of an integrable `f` from its average
`f_s = ⨍_s f` is at most twice its deviation from any constant `c`:

`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.

This is the Bochner-integral form, at `p = 1`, of the `Lᵖ` comparison
`TauCeti.eLpNorm_sub_setAverage_le`; its `L²` analogue, with factor `4`, is
`TauCeti.setIntegral_norm_sub_setAverage_sq_le`. In a real inner product space the average is the
best constant for the square deviation, with no loss, and this also holds for the averaged square
deviation: `⨍_s ‖f - f_s‖² ≤ ⨍_s ‖f - c‖²`.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul`: `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.
* `TauCeti.setAverage_norm_sub_setAverage_sq_le_setAverage_norm_sub_sq`:
  `⨍_s ‖f - f_s‖² ≤ ⨍_s ‖f - c‖²` in a real inner product space.
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

/-- In a real inner product space, the average of `g` over a set `s` of finite measure minimizes
the averaged square deviation: `⨍_s ‖g - g_s‖² ≤ ⨍_s ‖g - c‖²` for every constant `c`. -/
theorem setAverage_norm_sub_setAverage_sq_le_setAverage_norm_sub_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {g : X → E} (hs : μ s ≠ ⊤)
    (hg : IntegrableOn g s μ) {c : E} (hgc : IntegrableOn (fun x ↦ ‖g x - c‖ ^ 2) s μ) :
    ⨍ x in s, ‖g x - ⨍ y in s, g y ∂μ‖ ^ 2 ∂μ ≤ ⨍ x in s, ‖g x - c‖ ^ 2 ∂μ := by
  rw [setAverage_eq (f := fun x ↦ ‖g x - ⨍ y in s, g y ∂μ‖ ^ 2),
    setAverage_eq (f := fun x ↦ ‖g x - c‖ ^ 2), smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq hs hg hgc) (by positivity)

end TauCeti
