/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Unit-disk power series of complex and real logarithms

Mathlib's `Mathlib.Analysis.SpecialFunctions.Complex.Analytic` establishes local formal power
series germs (`HasFPowerSeriesAt`) for `Complex.log` and `Real.log` at `1` and for `1 + ·` at `0`,
while `Complex.hasSum_taylorSeries_neg_log` in
`Mathlib.Analysis.SpecialFunctions.Complex.LogBounds` proves pointwise convergence throughout the
open unit disk `‖z‖ < 1`.

Combining that pointwise Taylor sum with the coefficient bound `‖(n : ℂ)⁻¹‖ ≤ 1` upgrades the germ
statements to `HasFPowerSeriesOnBall` on the open unit disk of radius `1`:

## Main declarations

* `TauCeti.hasFPowerSeriesOnBall_neg_clog_one_sub`: `-Complex.log (1 - ·)` on `eball 0 1`.
* `TauCeti.hasFPowerSeriesOnBall_clog_one_add`: `Complex.log (1 + ·)` on `eball 0 1`.
* `TauCeti.hasFPowerSeriesOnBall_clog_one`: `Complex.log` on `eball 1 1`.
* `TauCeti.hasFPowerSeriesOnBall_neg_log_one_sub`: `-Real.log (1 - ·)` on `eball 0 1`.
* `TauCeti.hasFPowerSeriesOnBall_log_one_add`: `Real.log (1 + ·)` on `eball 0 1`.
* `TauCeti.hasFPowerSeriesOnBall_log_one`: `Real.log` on `eball 1 1`.
-/

public section

open scoped ENNReal

namespace TauCeti

/-- **The formal power series `∑ₙ zⁿ / n` represents `-Complex.log (1 - z)` on the unit disk.** -/
theorem hasFPowerSeriesOnBall_neg_clog_one_sub :
    HasFPowerSeriesOnBall (fun z : ℂ ↦ -Complex.log (1 - z))
      (.ofScalars ℂ fun n ↦ (n : ℂ)⁻¹) 0 1 := by
  refine ⟨FormalMultilinearSeries.le_radius_of_bound _ 1 fun n ↦ ?_, one_pos, fun {z} hz ↦ ?_⟩
  · simp only [NNReal.coe_one, one_pow, mul_one, FormalMultilinearSeries.ofScalars_norm, norm_inv,
      Complex.norm_natCast]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  · have hz1 : ‖z‖ < 1 := by
      simpa [Metric.mem_eball, edist_zero_right, ← ofReal_norm] using hz
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, div_eq_mul_inv] using
      Complex.hasSum_taylorSeries_neg_log hz1

/-- Transforming a unit-disk power series of `z ↦ -f (1 - z)` into that of `z ↦ f (1 + z)`. -/
private theorem hasFPowerSeriesOnBall_of_neg_sub {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f : 𝕜 → 𝕜} (hf : HasFPowerSeriesOnBall (fun z ↦ -f (1 - z))
      (.ofScalars 𝕜 fun n ↦ (n : 𝕜)⁻¹) 0 1) :
    HasFPowerSeriesOnBall (fun z ↦ f (1 + z)) (.ofScalars 𝕜 fun n ↦ -(-1 : 𝕜) ^ n / n) 0 1 := by
  have h0 : HasFPowerSeriesOnBall (fun z ↦ -f (1 - z))
      (.ofScalars 𝕜 fun n ↦ (n : 𝕜)⁻¹) ((-ContinuousLinearMap.id 𝕜 𝕜) 0) 1 := by
    simpa using hf
  convert h0.compContinuousLinearMap.neg using 1
  · ext z
    simp [sub_neg_eq_add]
  · rw [FormalMultilinearSeries.ofScalars_comp_neg_id]
    ext n
    simp [FormalMultilinearSeries.ofScalars, div_eq_mul_inv]
  · simp [← ofReal_norm, ContinuousLinearMap.norm_id]

/-- **The formal power series `∑ₙ -(-1)ⁿ zⁿ / n` represents `Complex.log (1 + z)` on the unit
disk.** This upgrades Mathlib's `hasFPowerSeriesAt_clog_one_add` to radius `1`. -/
theorem hasFPowerSeriesOnBall_clog_one_add :
    HasFPowerSeriesOnBall (fun z : ℂ ↦ Complex.log (1 + z))
      (.ofScalars ℂ fun n ↦ -(-1 : ℂ) ^ n / n) 0 1 :=
  hasFPowerSeriesOnBall_of_neg_sub hasFPowerSeriesOnBall_neg_clog_one_sub

/-- **The formal power series `∑ₙ -(-1)ⁿ (z - 1)ⁿ / n` represents `Complex.log` on the unit disk
around `1`.** This upgrades Mathlib's `hasFPowerSeriesAt_clog_one` to radius `1`. -/
theorem hasFPowerSeriesOnBall_clog_one :
    HasFPowerSeriesOnBall Complex.log (.ofScalars ℂ fun n ↦ -(-1 : ℂ) ^ n / n) 1 1 := by
  convert hasFPowerSeriesOnBall_clog_one_add.comp_sub (1 : ℂ) using 3 <;> ring

/-- **The formal power series `∑ₙ xⁿ / n` represents `-Real.log (1 - x)` on `(-1, 1)`.** -/
theorem hasFPowerSeriesOnBall_neg_log_one_sub :
    HasFPowerSeriesOnBall (fun x : ℝ ↦ -Real.log (1 - x))
      (.ofScalars ℝ fun n ↦ (n : ℝ)⁻¹) 0 1 := by
  have h : HasFPowerSeriesOnBall (fun z : ℂ ↦ -Complex.log (1 - z))
      ((FormalMultilinearSeries.ofScalars ℂ fun n : ℕ ↦ (n : ℂ)⁻¹).restrictScalars ℝ)
      (Complex.ofRealLI.toContinuousLinearMap 0) 1 := by
    simpa using hasFPowerSeriesOnBall_neg_clog_one_sub.restrictScalars (𝕜 := ℝ)
  have hre := Complex.reCLM.comp_hasFPowerSeriesOnBall h.compContinuousLinearMap
  have hrad : (1 : ℝ≥0∞) / ‖Complex.ofRealLI.toContinuousLinearMap‖ₑ = 1 := by simp
  have hser :
      Complex.reCLM.compFormalMultilinearSeries
        (((FormalMultilinearSeries.ofScalars ℂ fun n : ℕ ↦ (n : ℂ)⁻¹).restrictScalars
          ℝ).compContinuousLinearMap Complex.ofRealLI.toContinuousLinearMap) =
        .ofScalars ℝ fun n ↦ (n : ℝ)⁻¹ := by
    ext n
    simp [-FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.ofScalars, FormalMultilinearSeries.restrictScalars, List.prod_ofFn]
  rw [hrad, hser] at hre
  exact hre.congr fun x _ ↦ by simp [← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.log_ofReal_re]

/-- **The formal power series `∑ₙ -(-1)ⁿ xⁿ / n` represents `Real.log (1 + x)` on `(-1, 1)`.**
This upgrades Mathlib's `hasFPowerSeriesAt_log_one_add` to radius `1`. -/
theorem hasFPowerSeriesOnBall_log_one_add :
    HasFPowerSeriesOnBall (fun x : ℝ ↦ Real.log (1 + x))
      (.ofScalars ℝ fun n ↦ -(-1 : ℝ) ^ n / n) 0 1 :=
  hasFPowerSeriesOnBall_of_neg_sub hasFPowerSeriesOnBall_neg_log_one_sub

/-- **The formal power series `∑ₙ -(-1)ⁿ (x - 1)ⁿ / n` represents `Real.log` on `(0, 2)`.**
This upgrades Mathlib's `hasFPowerSeriesAt_log_one` to radius `1`. -/
theorem hasFPowerSeriesOnBall_log_one :
    HasFPowerSeriesOnBall Real.log (.ofScalars ℝ fun n ↦ -(-1 : ℝ) ^ n / n) 1 1 := by
  convert hasFPowerSeriesOnBall_log_one_add.comp_sub (1 : ℝ) using 3 <;> ring

end TauCeti
