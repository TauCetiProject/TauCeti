/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Comparing `ℓᵖ` seminorms on the counting measure

For the counting measure the `Lᵖ` seminorms decrease as the exponent grows: if `0 < p ≤ q`, then
`‖f‖_q ≤ ‖f‖_p`. This is the nesting `ℓᵖ ⊆ ℓ^q` of sequence spaces with its norm inequality, the
opposite of the inclusion `L^q ⊆ Lᵖ` on a probability space. Every value `‖f i‖` is bounded by
`‖f‖_p`, so `‖f i‖ ^ q ≤ ‖f‖_p ^ (q - p) ‖f i‖ ^ p`, and summing over `i` gives
`‖f‖_q ^ q ≤ ‖f‖_p ^ q`.

A geometric sequence `(rⁿ)` with `r < 1` lies in every `ℓ^q`. This is the summation behind the
embeddings of sequence spaces with polynomial or exponential weights, where a gain `2^{-εj}` in the
weight pays for any change of the summability exponent.

## Main declarations

* `MeasureTheory.eLpNorm_count_le_of_exponent_le`: `‖f‖_q ≤ ‖f‖_p` on `count` for `0 < p ≤ q`.
* `MeasureTheory.eLpNorm_count_lt_top_of_exponent_le`: the inclusion `ℓᵖ ⊆ ℓ^q`.
* `MeasureTheory.eLpNorm_count_pow_lt_top`: geometric sequences with ratio `r < 1` lie in `ℓ^q`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

open Measure

variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p q : ℝ≥0∞}

/-- **The `ℓᵖ` seminorms decrease in the exponent.** For the counting measure and
`0 < p ≤ q`, `‖f‖_q ≤ ‖f‖_p`. -/
theorem eLpNorm_count_le_of_exponent_le (hp : p ≠ 0) (hpq : p ≤ q) :
    eLpNorm f q count ≤ eLpNorm f p count := by
  by_cases hf : AEStronglyMeasurable f count
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]
  -- Every value is bounded by the `ℓᵖ` seminorm, which settles `q = ∞`.
  have hle i : ‖f i‖ₑ ≤ eLpNorm f p count := enorm_le_eLpNorm_count f i hp
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [eLpNorm_exponent_top hf, eLpNormEssSup_count]
    exact iSup_le hle
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have hq' : q ≠ 0 := ((pos_iff_ne_zero.2 hp).trans_le hpq).ne'
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq' hq
  have hpq' : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  -- The sum of the `p`-th powers is `A ^ p`.
  have hsum : ∑' i, ‖f i‖ₑ ^ p.toReal = eLpNorm f p count ^ p.toReal := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' hf, lintegral_count, one_div,
      ENNReal.rpow_inv_rpow hp0.ne']
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq' hq hf, lintegral_count, one_div,
    ENNReal.rpow_inv_le_iff hq0]
  calc ∑' i, ‖f i‖ₑ ^ q.toReal
      = ∑' i, ‖f i‖ₑ ^ (q.toReal - p.toReal) * ‖f i‖ₑ ^ p.toReal := by
        congr 1 with i
        rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hpq') hp0.le, sub_add_cancel]
    _ ≤ ∑' i, eLpNorm f p count ^ (q.toReal - p.toReal) * ‖f i‖ₑ ^ p.toReal :=
        tsum_le_tsum fun i ↦ by gcongr; exact hle i
    _ = eLpNorm f p count ^ q.toReal := by
        rw [ENNReal.tsum_mul_left, hsum, ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hpq')
          hp0.le, sub_add_cancel]

/-- **The inclusion `ℓᵖ ⊆ ℓ^q`** for `0 < p ≤ q`. -/
theorem eLpNorm_count_lt_top_of_exponent_le (hp : p ≠ 0) (hpq : p ≤ q)
    (hf : eLpNorm f p count < ∞) : eLpNorm f q count < ∞ :=
  (eLpNorm_count_le_of_exponent_le hp hpq).trans_lt hf

/-- **Geometric sequences are in every `ℓ^q`.** If `r < 1`, then `(rⁿ)ₙ` has finite `ℓ^q` norm
for every exponent `q`. -/
theorem eLpNorm_count_pow_lt_top {r : ℝ≥0∞} (hr : r < 1) (q : ℝ≥0∞) :
    eLpNorm (fun n : ℕ ↦ r ^ n) q count < ∞ := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [eLpNorm_exponent_zero .of_discrete]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [eLpNorm_exponent_top .of_discrete, eLpNormEssSup_count]
    exact (iSup_le fun n ↦ by simpa using pow_le_one₀ zero_le hr.le).trans_lt ENNReal.one_lt_top
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq .of_discrete, lintegral_count]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)
  -- The `q`-th powers form the geometric sequence with ratio `r ^ q < 1`.
  have hpow (n : ℕ) : ‖r ^ n‖ₑ ^ q.toReal = (r ^ q.toReal) ^ n := by
    rw [enorm_eq_self, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul, mul_comm]
  simp_rw [hpow, ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt (ENNReal.rpow_lt_one hr hq'))

end MeasureTheory
