/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# The `L¹` mean oscillation about the average

On a set `s` of finite measure, the `L¹` deviation of an integrable `f` from its average
`f_s = ⨍_s f` is at most twice its deviation from any constant `c`:

`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.

This is the Bochner-integral form, at `p = 1`, of the `Lᵖ` comparison
`TauCeti.eLpNorm_sub_setAverage_le`; its `L²` analogue, with factor `4`, is
`TauCeti.setIntegral_norm_sub_setAverage_sq_le`.

In a real inner product space, the square mean oscillation about the average on a subset `t ⊆ s`
is at most the `L²` mass on `s`: `∫_t ‖f - f_t‖² ≤ ∫_s ‖f‖²`.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul`: `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.
* `TauCeti.setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sq_of_subset`:
  `∫_t ‖f - f_t‖² ≤ ∫_s ‖f‖²` for `t ⊆ s`.
-/

public section

namespace TauCeti

open _root_.MeasureTheory

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

/-- **The square mean oscillation on a subset is at most the `L²` mass.** In a real inner product
space, for `f` square integrable on a set `s` of finite measure and `t ⊆ s`, the square mean
oscillation of `f` about its average over `t` is at most the `L²` mass of `f` over `s`:
`∫_t ‖f - f_t‖² ≤ ∫_s ‖f‖²`. -/
theorem setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sq_of_subset {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {g : X → E} {t : Set X}
    (hg : MemLp g 2 (μ.restrict s)) (hts : t ⊆ s) (hs : μ s ≠ ⊤) :
    ∫ x in t, ‖g x - ⨍ y in t, g y ∂μ‖ ^ 2 ∂μ ≤ ∫ x in s, ‖g x‖ ^ 2 ∂μ := by
  have ht : μ t ≠ ⊤ := ((measure_mono hts).trans_lt hs.lt_top).ne
  have h := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq ht
    (hg.integrableOn_of_subset one_le_two hts ht) (hg.integrableOn_norm_sub_sq_of_subset hts ht 0)
  have hgs := hg.integrableOn_norm_sub_sq_of_subset subset_rfl hs 0
  simp only [sub_zero] at h hgs
  exact h.trans (setIntegral_mono_set hgs (ae_of_all _ fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall hts))

end TauCeti
