/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fourth-moment bounds for clipping

For `M > 0`, clipping a real number to `[-M, M]` has squared error at most its fourth
power divided by `16 M²`. Integrating this estimate controls the `L²` error of clipping a random
variable using only its fourth moment. In particular it applies to Gaussian linear
observables in the truncation proof of Grothendieck's inequality.

The expression `max (-M) (min M x)` is the real-valued form of `Set.projIcc`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Real

/-- Clipping to a symmetric interval does not increase absolute value. -/
theorem abs_max_min_le_abs {M : ℝ} (hM : 0 ≤ M) (x : ℝ) :
    |max (-M) (min M x)| ≤ |x| := by
  rcases le_total x (-M) with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx, abs_neg, abs_of_nonneg hM,
      abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total x M with hx' | hx'
    · simp [min_eq_right hx', max_eq_right hx]
    · rw [min_eq_left hx', max_eq_right (by linarith), abs_of_nonneg hM,
        abs_of_nonneg (by linarith)]
      exact hx'

/-- The pointwise fourth-moment estimate for clipping, with the sharp constant `1/16`. -/
theorem sq_sub_max_min_le_pow_four_div {M : ℝ} (hM : 0 < M) (x : ℝ) :
    (x - max (-M) (min M x)) ^ 2 ≤ x ^ 4 / (16 * M ^ 2) := by
  have tail (t : ℝ) (ht : M ≤ t) : (t - M) ^ 2 ≤ t ^ 4 / (16 * M ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 16 * M ^ 2)).2
    have h : 4 * M * (t - M) ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 2 * M)]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * M * (t - M)) h 2
    nlinarith only [hh]
  rcases le_total x (-M) with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx]
    convert tail (-x) (by linarith) using 1 <;> ring
  · rcases le_total x M with hx' | hx'
    · simp only [min_eq_right hx', max_eq_right hx, sub_self, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · rw [min_eq_left hx', max_eq_right (by linarith)]
      exact tail x hx'

end Real

namespace MeasureTheory.MemLp

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-- Clipping a real `Lᵖ` function to a symmetric interval preserves `Lᵖ` membership,
without a finiteness assumption on the measure. -/
theorem max_min {p : ℝ≥0∞} (hf : MemLp f p μ) {M : ℝ} (hM : 0 ≤ M) :
    MemLp (fun x ↦ max (-M) (min M (f x))) p μ := by
  have hcont : Continuous (fun t : ℝ ↦ max (-M) (min M t)) := by fun_prop
  refine hf.norm.mono' (hcont.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x ↦ Real.abs_max_min_le_abs hM (f x)

/-- The squared `L²` clipping error is bounded by the fourth moment divided by `16 M²`. -/
theorem integral_sq_sub_max_min_le (hf : MemLp f 2 μ)
    (hf₄ : Integrable (fun x ↦ f x ^ 4) μ) {M : ℝ} (hM : 0 < M) :
    (∫ x, (f x - max (-M) (min M (f x))) ^ 2 ∂μ) ≤
      (∫ x, f x ^ 4 ∂μ) / (16 * M ^ 2) := by
  rw [← integral_div]
  exact integral_mono ((hf.sub (hf.max_min hM.le)).integrable_sq) (hf₄.div_const _)
    fun x ↦ Real.sq_sub_max_min_le_pow_four_div hM (f x)

end MeasureTheory.MemLp
