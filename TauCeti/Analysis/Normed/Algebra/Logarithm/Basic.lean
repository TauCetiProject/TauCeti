/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Algebra.Logarithm

import TauCeti.Analysis.Normed.Field.NatCast

/-!
# Convergence of the logarithm series in a Banach algebra

Mathlib defines the logarithm `NormedSpace.log x = ∑ n ≥ 1, (-1)^(n+1) / n • (x - 1)^n` as the
sum of `NormedSpace.logSeries` at `x - 1`. This file establishes the convergence and analyticity
of `NormedSpace.logSeries` and `NormedSpace.log`: in a Banach algebra over a characteristic-zero
normed field, the radius of convergence of `NormedSpace.logSeries` is at least one, so
`NormedSpace.log` is analytic at one.
It supplies the local logarithm needed to define the Baker–Campbell–Hausdorff map near the
origin.

## Main results

* `NormedSpace.logSeries_apply`: the homogeneous terms of `NormedSpace.logSeries`.
* `NormedSpace.logSeries_partialSum_three`: its third partial sum, `u - 2⁻¹ • u ^ 2`.
* `NormedSpace.one_le_logSeries_radius`: the radius of convergence is at least one.
* `NormedSpace.log_hasFPowerSeriesOnBall`: the series represents `NormedSpace.log` on the
  unit ball about one.
* `NormedSpace.isBigO_log_one_add_sub_quadratic`: `log (1 + u) - (u - 2⁻¹ • u ^ 2)` is
  `O(‖u‖ ^ 3)` at the origin.
-/

public section

open Asymptotics Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace NormedSpace

section Algebra

variable (𝕂 A : Type*) [Field 𝕂] [Ring A] [Algebra 𝕂 A]
variable [TopologicalSpace A] [IsTopologicalRing A]

/-- The homogeneous terms of `logSeries`. -/
@[simp]
theorem logSeries_apply {n : ℕ} (v : Fin n → A) :
    logSeries 𝕂 A n v = ((-1 : 𝕂) ^ (n + 1) / n) • (List.ofFn v).prod := by
  simp only [logSeries, smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply]

/-- The third partial sum of the series for `log (1 + u)` is the quadratic truncation
`u - 2⁻¹ • u ^ 2`. -/
@[simp]
theorem logSeries_partialSum_three (u : A) :
    (logSeries 𝕂 A).partialSum 3 u = u - (2⁻¹ : 𝕂) • u ^ 2 := by
  simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, logSeries_apply, List.ofFn_const, List.prod_replicate]
  norm_num [neg_div, neg_smul, sub_eq_add_neg]

end Algebra

section Normed

variable (𝕂 A : Type*) [NontriviallyNormedField 𝕂]
variable [NormedRing A] [NormedAlgebra 𝕂 A]

/-- The radius of `logSeries` is at least one. -/
theorem one_le_logSeries_radius : 1 ≤ (logSeries 𝕂 A).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.1 hr
  obtain ⟨B, hB⟩ := (NormedField.tendsto_norm_inv_natCast_mul_pow 𝕂 r.2 hr1).bddAbove_range
  refine FormalMultilinearSeries.le_radius_of_bound _ (max B ‖logSeries 𝕂 A 0‖) fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · calc ‖logSeries 𝕂 A n‖ * (r : ℝ) ^ n ≤ ‖(n : 𝕂)⁻¹‖ * (r : ℝ) ^ n := by
          gcongr
          rw [logSeries_eq_ofScalars]
          refine (FormalMultilinearSeries.ofScalars_norm_le A _ n hn).trans (le_of_eq ?_)
          simp [norm_div, norm_inv]
      _ ≤ B := hB ⟨n, rfl⟩
      _ ≤ max B ‖logSeries 𝕂 A 0‖ := le_max_left _ _

variable [CompleteSpace A]

/-- The series for `log (1 + u)` is summable in the open unit ball. -/
theorem logSeries_summable_of_norm_lt_one {u : A} (hu : ‖u‖ < 1) :
    Summable fun n : ℕ ↦ ((-1 : 𝕂) ^ (n + 1) / n) • u ^ n := by
  simpa only [logSeries_apply_eq] using (logSeries 𝕂 A).summable
    (Metric.eball_subset_eball (one_le_logSeries_radius 𝕂 A) (by simpa [← ofReal_norm] using hu))

variable [CharZero 𝕂]

/-- `logSeries` represents `log` throughout the open unit ball about one. -/
theorem log_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall (log : A → A) (logSeries 𝕂 A) 1 1 := by
  have h := ((logSeries 𝕂 A).hasFPowerSeriesOnBall
    (one_pos.trans_le (one_le_logSeries_radius 𝕂 A))).mono one_pos (one_le_logSeries_radius 𝕂 A)
  rw [log_eq_logSeries_sum 𝕂]
  simpa only [zero_add] using h.comp_sub 1

/-- `log` is analytic at one. -/
theorem analyticAt_log_one : AnalyticAt 𝕂 (log : A → A) 1 :=
  log_hasFPowerSeriesOnBall 𝕂 A |>.analyticAt

/-- **The quadratic Taylor estimate for the Banach algebra logarithm.**  The difference
`log (1 + u) - (u - 2⁻¹ • u ^ 2)` is `O(‖u‖ ^ 3)` as `u → 0`. -/
theorem isBigO_log_one_add_sub_quadratic :
    (fun u : A ↦ log (1 + u) - (u - (2⁻¹ : 𝕂) • u ^ 2)) =O[𝓝 (0 : A)] fun u ↦ ‖u‖ ^ 3 := by
  simpa only [logSeries_partialSum_three] using
    (log_hasFPowerSeriesOnBall 𝕂 A).hasFPowerSeriesAt.isBigO_sub_partialSum_pow 3

end Normed

end NormedSpace
