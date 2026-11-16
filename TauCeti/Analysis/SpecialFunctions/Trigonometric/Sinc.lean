/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import TauCeti.Analysis.Analytic.OfScalars

/-!
# Scaled sinc derivatives and even cosine and sinc-squared series

For `ω ≠ 0` the function `t ↦ t sinc (ω t)` is `t ↦ sin (ω t) / ω`, and for `ω = 0` it is the
identity. Either way its derivative is `t ↦ cos (ω t)`, so it is the solution of
`f'' = -ω² f` with `f 0 = 0` and `f' 0 = 1`, uniformly in the frequency `ω`, including the
degenerate frequency `0`.

This file also packages the entire even cosine power series `Real.evenCosSeries` (`s ↦ cos √s` for
`s = x²`) and its divided-difference quotient `Real.evenSincSq`, the entire real-analytic function
satisfying `evenSincSq (x ^ 2) = sinc x ^ 2` for every `x : ℝ`.
-/

public section

namespace Real

/-- `x sinc x = sin x` for every real `x`, including `x = 0`. -/
@[simp]
theorem mul_sinc (x : ℝ) : x * sinc x = sin x := by
  simpa [sinc_eq_dslope] using sub_smul_dslope sin 0 x

/-- For `ω ≠ 0`, `t sinc (ω t) = sin (ω t) / ω`. -/
theorem mul_sinc_mul_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    t * sinc (ω * t) = sin (ω * t) / ω := by
  rw [eq_div_iff hω, ← mul_sinc]
  ring

/-- The derivative of `t ↦ t sinc (ω t)` is `cos (ω t)`, for every frequency `ω`. -/
theorem hasDerivAt_mul_sinc_mul (ω t : ℝ) :
    HasDerivAt (fun s ↦ s * sinc (ω * s)) (cos (ω * t)) t := by
  rcases eq_or_ne ω 0 with rfl | hω
  · simpa using hasDerivAt_id' t
  · simp_rw [mul_sinc_mul_of_ne_zero hω]
    convert ((hasDerivAt_id' t).const_mul ω).sin.div_const ω using 1
    field_simp

/-- The formal power series `∑ (-1)^k s^k / (2k)!`, whose sum at `x²` is `cos x`. -/
noncomputable def evenCosSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun k ↦ (-1 : ℝ) ^ k / (2 * k).factorial

/-- `Real.evenCosSeries` has infinite radius of convergence. -/
@[simp]
theorem evenCosSeries_radius : evenCosSeries.radius = ⊤ := by
  refine evenCosSeries.radius_eq_top_of_summable_norm fun r ↦
    (hasSum_cosh √(r : ℝ)).summable.congr fun k ↦ ?_
  simp [evenCosSeries, pow_mul, sq_sqrt r.coe_nonneg]
  ring

/-- The sum of `Real.evenCosSeries` is real-analytic on all of `ℝ`. -/
theorem analyticOnNhd_evenCosSeries_sum : AnalyticOnNhd ℝ evenCosSeries.sum Set.univ := by
  simpa [evenCosSeries_radius] using evenCosSeries.analyticOnNhd

/-- Evaluating `Real.evenCosSeries.sum` at `x ^ 2` gives `cos x`. -/
@[simp]
theorem evenCosSeries_sum_sq (x : ℝ) : evenCosSeries.sum (x ^ 2) = cos x := by
  rw [evenCosSeries, ← FormalMultilinearSeries.ofScalarsSum,
    FormalMultilinearSeries.ofScalars_sum_eq, cos_eq_tsum x]
  exact tsum_congr fun k ↦ by rw [smul_eq_mul, ← pow_mul]; ring

@[simp]
theorem evenCosSeries_sum_zero : evenCosSeries.sum 0 = 1 := by
  simpa using evenCosSeries_sum_sq 0

/-- The derivative of `Real.evenCosSeries.sum` at `0` is `-1 / 2`. -/
@[simp]
theorem deriv_evenCosSeries_sum_zero : deriv evenCosSeries.sum 0 = -(1 / 2) := by
  have h := FormalMultilinearSeries.iteratedDeriv_ofScalarsSum_zero
    (fun k ↦ (-1 : ℝ) ^ k / (2 * k).factorial)
    (by rw [← evenCosSeries, evenCosSeries_radius]; exact ENNReal.zero_lt_top) 1
  rw [iteratedDeriv_one, FormalMultilinearSeries.ofScalarsSum, ← evenCosSeries] at h
  norm_num [Nat.factorial] at h
  exact h

/-- The entire real-analytic function `s ↦ (1 - cos (2 √s)) / (2 s)` (extended to `1` at `0`),
whose value at `x ^ 2` is `sinc x ^ 2` for every real `x`. -/
noncomputable def evenSincSq : ℝ → ℝ :=
  dslope (fun s : ℝ ↦ 2⁻¹ * (1 - evenCosSeries.sum (4 * s))) 0

/-- `Real.evenSincSq` is real-analytic on all of `ℝ`. -/
theorem analyticOnNhd_evenSincSq : AnalyticOnNhd ℝ evenSincSq Set.univ :=
  (analyticOnNhd_const.mul (analyticOnNhd_const.sub (analyticOnNhd_evenCosSeries_sum.comp
    (analyticOnNhd_const.mul analyticOnNhd_id) (Set.mapsTo_univ _ _)))).dslope 0

@[simp]
theorem evenSincSq_zero : evenSincSq 0 = 1 := by
  have h0 : HasDerivAt evenCosSeries.sum (deriv evenCosSeries.sum 0) (4 * (0 : ℝ)) := by
    rw [mul_zero]
    exact (analyticOnNhd_evenCosSeries_sum 0 trivial).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun s : ℝ ↦ 2⁻¹ * (1 - evenCosSeries.sum (4 * s)))
      (2⁻¹ * (0 - deriv evenCosSeries.sum 0 * (4 * 1))) 0 :=
    ((hasDerivAt_const 0 (1 : ℝ)).sub (h0.comp 0 ((hasDerivAt_id' 0).const_mul 4))).const_mul 2⁻¹
  rw [evenSincSq, dslope_same, hd.deriv, deriv_evenCosSeries_sum_zero]
  ring

/-- Evaluating `Real.evenSincSq` at `x ^ 2` gives `sinc x ^ 2` for every `x : ℝ`. -/
@[simp]
theorem evenSincSq_sq (x : ℝ) : evenSincSq (x ^ 2) = sinc x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h4 : 4 * x ^ 2 = (2 * x) ^ 2 := by ring
    have htrig : 2⁻¹ * (1 - cos (2 * x)) = sin x ^ 2 := by
      rw [cos_two_mul', cos_sq']; ring
    simp [evenSincSq, dslope_of_ne _ (pow_ne_zero 2 hx), slope_def_field, h4, htrig,
      sinc_of_ne_zero hx, div_pow]

end Real
