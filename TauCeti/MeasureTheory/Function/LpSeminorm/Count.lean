/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-!
# Comparison of `ℓᵖ` norms

For the counting measure, the `Lᵖ` seminorm of `f` is the `ℓᵖ` norm `(∑ᵢ ‖f i‖ᵖ)^{1/p}`, and
`supᵢ ‖f i‖` for `p = ∞`. Unlike the `Lᵖ` seminorms on a probability space, which increase with
the exponent (`MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le`), the `ℓᵖ` norms decrease:
`‖f‖_{ℓʳ} ≤ ‖f‖_{ℓ^q}` for `0 < q ≤ r ≤ ∞`, so `ℓ^q ⊆ ℓʳ`. Every term of a sequence is bounded
by its `ℓ^q` norm, which gives the case `r = ∞`, and for finite `r` one writes
`‖f i‖ʳ = ‖f i‖^q ‖f i‖^{r - q}` and bounds the second factor by the `ℓ^q` norm.

This is the inclusion of sequence spaces behind the monotonicity in the summability index of
Besov spaces.

## Main declarations

* `MeasureTheory.eLpNorm_count_le_of_exponent_le`: `‖f‖_{ℓʳ} ≤ ‖f‖_{ℓ^q}` for `0 < q ≤ r`.
-/

public section

open ENNReal

namespace MeasureTheory

variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}

/-- **The `ℓᵖ` norms decrease with the exponent.** For the counting measure and
`0 < q ≤ r ≤ ∞`, `‖f‖_{ℓʳ} ≤ ‖f‖_{ℓ^q}`. -/
theorem eLpNorm_count_le_of_exponent_le {q r : ℝ≥0∞} (hq : q ≠ 0) (hqr : q ≤ r) :
    eLpNorm f r .count ≤ eLpNorm f q .count := by
  set N := eLpNorm f q .count with hN_def
  rcases eq_top_or_lt_top N with hN | hN
  · exact hN ▸ le_top
  have hf : AEStronglyMeasurable f .count := aestronglyMeasurable_of_eLpNorm_ne_top hN.ne
  have hbound (i : α) : ‖f i‖ₑ ≤ N := enorm_le_eLpNorm_count f i hq
  rcases eq_or_ne r ∞ with rfl | hr
  · rw [eLpNorm_exponent_top hf]
    exact eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ hbound)
  have hq_top : q ≠ ∞ := ne_top_of_le_ne_top hr hqr
  have hr0 : r ≠ 0 := (pos_iff_ne_zero.2 hq |>.trans_le hqr).ne'
  have hq0 : 0 < q.toReal := toReal_pos hq hq_top
  have hqr' : q.toReal ≤ r.toReal := toReal_mono hr hqr
  -- `N ^ q = ∑ᵢ ‖f i‖ ^ q`.
  have hNq : ∑' i, ‖f i‖ₑ ^ q.toReal = N ^ q.toReal := by
    rw [hN_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hq hq_top hf, lintegral_count, one_div,
      rpow_inv_rpow hq0.ne']
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr hf, lintegral_count]
  calc (∑' i, ‖f i‖ₑ ^ r.toReal) ^ (1 / r.toReal)
      ≤ (∑' i, ‖f i‖ₑ ^ q.toReal * N ^ (r.toReal - q.toReal)) ^ (1 / r.toReal) := by
        gcongr with i
        rw [← add_sub_cancel q.toReal r.toReal, rpow_add_of_nonneg _ _ hq0.le (sub_nonneg.2 hqr'),
          add_sub_cancel]
        gcongr
        exact hbound i
    _ = N := by
        rw [ENNReal.tsum_mul_right, hNq, ← rpow_add_of_nonneg _ _ hq0.le (sub_nonneg.2 hqr'),
          add_sub_cancel, one_div, rpow_rpow_inv (toReal_pos hr0 hr).ne']

end MeasureTheory
