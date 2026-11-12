/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Algebra.Order.Group.MinMax
public import TauCeti.Algebra.Order.Field.Clipping

/-!
# Fourth-moment bounds for clipping

`MeasureTheory.MemLp.max_min` shows that clipping a real `Lᵖ` function to `[-M, M]`, for
`0 ≤ M`, preserves `Lᵖ` membership for any measure. For `M > 0`,
`MeasureTheory.Integrable.integral_sq_sub_max_min_le` bounds the integrated squared clipping
error by the fourth moment divided by `16 M²`, using the pointwise inequality from
`TauCeti.Algebra.Order.Field.Clipping`. This controls the `L²` error of clipping Gaussian
linear observables in the truncation proof of Grothendieck's inequality.

The expression `max (-M) (min M x)` is the real-valued form of `Set.projIcc`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-- Clipping a real `Lᵖ` function to a symmetric interval preserves `Lᵖ` membership,
without a finiteness assumption on the measure. -/
theorem MemLp.max_min {p : ℝ≥0∞} (hf : MemLp f p μ) {M : ℝ} (hM : 0 ≤ M) :
    MemLp (fun x ↦ max (-M) (min M (f x))) p μ := by
  have hcont : Continuous (fun t : ℝ ↦ max (-M) (min M t)) := by fun_prop
  refine hf.norm.mono' (hcont.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x ↦ TauCeti.abs_max_min_le_abs hM (f x)

/-- The squared `L²` clipping error is bounded by the fourth moment divided by `16 M²`. -/
theorem Integrable.integral_sq_sub_max_min_le
    (hf₄ : Integrable (fun x ↦ f x ^ 4) μ) {M : ℝ} (hM : 0 < M) :
    (∫ x, (f x - max (-M) (min M (f x))) ^ 2 ∂μ) ≤
      (∫ x, f x ^ 4 ∂μ) / (16 * M ^ 2) := by
  rw [← integral_div]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
    (hf₄.div_const _)
    (Filter.Eventually.of_forall fun x ↦ TauCeti.sq_sub_max_min_le_pow_four_div hM (f x))

end MeasureTheory
