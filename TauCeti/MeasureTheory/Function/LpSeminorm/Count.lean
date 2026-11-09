/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-!
# Nesting of the `ℓᵖ` seminorms

For the counting measure the `Lᵖ` seminorms decrease as the exponent grows:
`‖f‖_{ℓ^q} ≤ ‖f‖_{ℓ^p}` for `0 < p ≤ q ≤ ∞`. This is the seminorm form of the inclusion
`ℓᵖ ⊆ ℓ^q` (`Memℓp.of_exponent_ge`, `lp.monotone`), stated for the extended seminorm
`eLpNorm · · count`, so that it applies to `ℝ≥0∞`-valued sequences as well.

The proof is the classical one: every term is at most `‖f‖_{ℓᵖ}`, so
`∑ ‖f i‖^q = ∑ ‖f i‖^p ‖f i‖^{q - p} ≤ ‖f‖_{ℓᵖ}^{q - p} ∑ ‖f i‖^p = ‖f‖_{ℓᵖ}^q`.

## Main statements

* `MeasureTheory.eLpNorm_count_le_of_exponent_le`: `‖f‖_{ℓ^q} ≤ ‖f‖_{ℓ^p}` for `0 < p ≤ q`.
* `MeasureTheory.eLpNorm_pow_count_lt_top`: a geometric sequence with ratio `a < 1` lies in every
  `ℓ^q`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

open Measure

variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p q : ℝ≥0∞}

/-- **Nesting of the `ℓᵖ` seminorms.** For the counting measure, the `Lᵖ` seminorm decreases as
the exponent grows: `‖f‖_{ℓ^q} ≤ ‖f‖_{ℓᵖ}` whenever `0 < p ≤ q`. -/
theorem eLpNorm_count_le_of_exponent_le (hp : p ≠ 0) (hpq : p ≤ q) :
    eLpNorm f q count ≤ eLpNorm f p count := by
  by_cases hf : AEStronglyMeasurable f count
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]
  have hle (i : α) : ‖f i‖ₑ ≤ eLpNorm f p count := enorm_le_eLpNorm_count f i hp
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [eLpNorm_exponent_top hf, eLpNormEssSup_count]
    exact iSup_le hle
  have hp' : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  set N := eLpNorm f p count with hN
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have hPQ : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  have hQ : 0 < q.toReal := hP.trans_le hPQ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hp.bot_lt.trans_le hpq).ne' hq hf, lintegral_count]
  -- The `p`-th power sum of `f` is `N ^ p`.
  have hsum : ∑' i, ‖f i‖ₑ ^ p.toReal = N ^ p.toReal := by
    rw [hN, eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp' hf, lintegral_count,
      ← ENNReal.rpow_mul, one_div_mul_cancel hP.ne', ENNReal.rpow_one]
  calc (∑' i, ‖f i‖ₑ ^ q.toReal) ^ (1 / q.toReal)
      ≤ (∑' i, N ^ (q.toReal - p.toReal) * ‖f i‖ₑ ^ p.toReal) ^ (1 / q.toReal) := by
        gcongr with i
        calc ‖f i‖ₑ ^ q.toReal = ‖f i‖ₑ ^ (q.toReal - p.toReal) * ‖f i‖ₑ ^ p.toReal := by
              rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hPQ) hP.le, sub_add_cancel]
          _ ≤ N ^ (q.toReal - p.toReal) * ‖f i‖ₑ ^ p.toReal := by
              gcongr
              exact hle i
    _ = N := by
        rw [ENNReal.tsum_mul_left, hsum, ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hPQ) hP.le,
          sub_add_cancel, ← ENNReal.rpow_mul, mul_one_div_cancel hQ.ne', ENNReal.rpow_one]

/-- A **geometric sequence** with ratio `a < 1` lies in every `ℓ^q`. -/
theorem eLpNorm_pow_count_lt_top {a : ℝ≥0∞} (ha : a < 1) (q : ℝ≥0∞) :
    eLpNorm (fun j : ℕ ↦ a ^ j) q count < ∞ := by
  have hm : AEStronglyMeasurable (fun j : ℕ ↦ a ^ j) count :=
    StronglyMeasurable.of_discrete.aestronglyMeasurable
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [hm]
  rcases eq_or_ne q ∞ with rfl | hq
  · rw [eLpNorm_exponent_top hm, eLpNormEssSup_count]
    exact (iSup_le fun j ↦ by simpa using pow_le_one₀ bot_le ha.le).trans_lt ENNReal.one_lt_top
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hm, lintegral_count]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)
  simp_rw [enorm_eq_self, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm _ q.toReal,
    ENNReal.rpow_mul, ENNReal.rpow_natCast, ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt (ENNReal.rpow_lt_one ha hQ))

end MeasureTheory
