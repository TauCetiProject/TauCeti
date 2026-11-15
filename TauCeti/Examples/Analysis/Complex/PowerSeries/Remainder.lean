/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.MultiIndex
public import TauCeti.Analysis.Complex.PowerSeries.Remainder
public import TauCeti.Analysis.Complex.Schwarz
import TauCeti.Analysis.Analytic.Order

/-!
# Examples and sharpness checks for Cauchy and Taylor remainder bounds

This file instantiates the Schwarz, Cauchy, and truncated Taylor remainder bounds on concrete
functions and records boundary counterexamples showing that the strict interior hypothesis
`‖z‖ < R` on evaluation points and the positivity hypothesis `1 ≤ T` on asymptotic order cannot be
dropped.

1. For `g w = w ^ 2` on `ball (0 : ℂ) 2` (`M = 4`, `T = 2`) at `w = 1`,
   `Complex.norm_le_mul_div_pow_of_le_analyticOrderAt` gives `1 ≤ 4 * (1 / 2) ^ 2 = 1`, attaining
   equality.
2. For `F z = z ^ 2` on `ball (0 : ℂ) 2` (`R = 2`, `M = 4`), Cauchy's homogeneous bound
   `HasFPowerSeriesOnBall.norm_apply_mul_pow_le` at `n = 2`, `v = 1` gives `1 * 2 ^ 2 ≤ 4`, and at
   `z = 1` the remainders `‖F 1 - p.partialSum T 1‖` for `T = 0, 2, 3` equal `1, 1, 0` against the
   `(1 + T) * M * (1 / 2) ^ T` bounds `4, 3, 2` from
   `HasFPowerSeriesOnBall.norm_sub_partialSum_le`.
3. On `Fin 2 → ℂ`, representing `z ↦ z 0 * z 1` on `ball 0 2` (`M = 4`) by the non-symmetric
   bilinear map `(u, v) ↦ u 0 * v 1` gives `p.mvCoeff ![1, 1] = 1`, and
   `HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le` at the boundary radius `ρ = 2` attains
   `1 * 2 ^ 2 = 4`.
4. Modifying `0 : ℂ → ℂ` outside the open unit disc (`f z = if ‖z‖ < 1 then 0 else 1`) preserves
   `HasFPowerSeriesOnBall f 0 0 1` while violating the remainder bound at `z = 1`, and
   `g w = if w = 0 then 0 else 1` shows that
   `TauCeti.isLittleO_sub_pow_sub_one_of_le_analyticOrderAt` fails at `T = 0`.
-/

public section

open Filter Finset Metric Topology
open scoped ENNReal NNReal

namespace TauCeti.PowerSeriesRemainderExample

/-! ### 1. Sharpness of `Complex.norm_le_mul_div_pow_of_le_analyticOrderAt` -/

theorem analyticOrderAt_sq_zero : (2 : ℕ∞) ≤ analyticOrderAt (fun w : ℂ ↦ w ^ 2) 0 := by
  have h : (fun w : ℂ ↦ w ^ 2) = (· - 0) ^ 2 := funext fun w ↦ by simp
  rw [h, analyticOrderAt_centeredMonomial]
  rfl

theorem norm_sq_le_four {w : ℂ} (hw : w ∈ ball (0 : ℂ) 2) : ‖w ^ 2‖ ≤ 4 := by
  have hw' : ‖w‖ < 2 := by simpa using hw
  calc ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow w 2
    _ ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hw'.le 2
    _ = 4 := by norm_num

/-- At `w = 1` on `ball 0 2` (`M = 4`, `T = 2`), both sides of
`Complex.norm_le_mul_div_pow_of_le_analyticOrderAt` for `w ↦ w ^ 2` equal `1`. -/
example : ‖(1 : ℂ) ^ 2‖ ≤ 4 * (‖(1 : ℂ) - 0‖ / 2) ^ 2 ∧
    (‖(1 : ℂ) ^ 2‖ = 1 ∧ 4 * (‖(1 : ℂ) - 0‖ / 2) ^ 2 = (1 : ℝ)) :=
  ⟨Complex.norm_le_mul_div_pow_of_le_analyticOrderAt (g := fun w : ℂ ↦ w ^ 2)
    (by fun_prop) (fun _ hw ↦ norm_sq_le_four hw) analyticOrderAt_sq_zero (by simp), by norm_num⟩

/-! ### 2. Scalar quadratic `F z = z ^ 2` on `ball (0 : ℂ) 2` -/

/-- Formal power series of `z ↦ z ^ 2` at `0`: `ofScalars ℂ (Pi.single 2 1)`. -/
noncomputable def sqSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (Pi.single 2 1)

theorem sqSeries_apply (k : ℕ) (z : ℂ) :
    sqSeries k (fun _ ↦ z) = if k = 2 then z ^ 2 else 0 := by
  simp [sqSeries, Pi.single_apply]
  split_ifs with hk
  · simp [hk]
  · simp

theorem hasFPowerSeriesOnBall_sq :
    HasFPowerSeriesOnBall (fun z : ℂ ↦ z ^ 2) sqSeries 0 (2 : ℝ≥0) where
  r_le := sqSeries.le_radius_of_eventually_le 0 <| eventually_atTop.2 ⟨3, fun k hk ↦ by
    have hk2 : k ≠ 2 := by omega
    have h0 : sqSeries k = 0 := by
      ext
      simp [sqSeries, FormalMultilinearSeries.ofScalars, Pi.single_eq_of_ne hk2]
    simp [h0]⟩
  r_pos := by simp
  hasSum {z} _ := by
    have h := hasSum_single (f := fun k ↦ sqSeries k (fun _ ↦ z)) 2 fun k hk ↦ by
      rw [sqSeries_apply]
      simp [hk]
    rw [sqSeries_apply] at h
    simpa using h

/-- Cauchy's homogeneous bound `HasFPowerSeriesOnBall.norm_apply_mul_pow_le` attains equality
`4 = 4` for `z ↦ z ^ 2` at `n = 2`, `v = 1`, `R = 2`. -/
example : ‖sqSeries 2 (fun _ ↦ (1 : ℂ))‖ * ((2 : ℝ≥0) : ℝ) ^ 2 ≤ 4 * ‖(1 : ℂ)‖ ^ 2 ∧
    ‖sqSeries 2 (fun _ ↦ (1 : ℂ))‖ * ((2 : ℝ≥0) : ℝ) ^ 2 = 4 := by
  refine ⟨hasFPowerSeriesOnBall_sq.norm_apply_mul_pow_le (fun _ hy ↦ norm_sq_le_four hy) 2 1, ?_⟩
  rw [sqSeries_apply]
  norm_num

/-- Truncated Taylor remainder bounds `HasFPowerSeriesOnBall.norm_sub_partialSum_le` for
`z ↦ z ^ 2` on `ball 0 2` at `z = 1` for `T = 0, 2, 3` (`1 ≤ 4`, `1 ≤ 3`, `0 ≤ 2`). -/
example :
    (‖(1 : ℂ) ^ 2 - sqSeries.partialSum 0 1‖ ≤ (1 + (0 : ℕ)) * 4 * (‖(1 : ℂ)‖ / (2 : ℝ≥0)) ^ 0) ∧
    (‖(1 : ℂ) ^ 2 - sqSeries.partialSum 2 1‖ ≤ (1 + (2 : ℕ)) * 4 * (‖(1 : ℂ)‖ / (2 : ℝ≥0)) ^ 2) ∧
    (‖(1 : ℂ) ^ 2 - sqSeries.partialSum 3 1‖ ≤ (1 + (3 : ℕ)) * 4 * (‖(1 : ℂ)‖ / (2 : ℝ≥0)) ^ 3) ∧
    ‖(1 : ℂ) ^ 2 - sqSeries.partialSum 3 1‖ = 0 := by
  have hz : ‖(1 : ℂ)‖ < (2 : ℝ≥0) := by norm_num
  refine ⟨hasFPowerSeriesOnBall_sq.norm_sub_partialSum_le (fun _ hy ↦ norm_sq_le_four hy) 0 hz,
    hasFPowerSeriesOnBall_sq.norm_sub_partialSum_le (fun _ hy ↦ norm_sq_le_four hy) 2 hz,
    hasFPowerSeriesOnBall_sq.norm_sub_partialSum_le (fun _ hy ↦ norm_sq_le_four hy) 3 hz, ?_⟩
  simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, sqSeries_apply]
  norm_num

/-! ### 3. Non-symmetric bilinear series on `Fin 2 → ℂ` -/

/-- The non-symmetric bilinear map `(u, v) ↦ u 0 * v 1` on `Fin 2 → ℂ`, packaged as the single
degree-`2` term of a formal multilinear series. -/
noncomputable def prodSeries : FormalMultilinearSeries ℂ (Fin 2 → ℂ) ℂ := fun k ↦
  if h : k = 2 then
    h ▸ (ContinuousMultilinearMap.mkPiAlgebraFin ℂ 2 ℂ).compContinuousLinearMap
      ![ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0,
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1]
  else 0

theorem prodSeries_two_apply (m : Fin 2 → Fin 2 → ℂ) :
    prodSeries 2 m = m 0 0 * m 1 1 := by
  simp [prodSeries, ContinuousMultilinearMap.mkPiAlgebraFin_apply]

theorem hasFPowerSeriesOnBall_prod :
    HasFPowerSeriesOnBall (fun z : Fin 2 → ℂ ↦ z 0 * z 1) prodSeries 0 (2 : ℝ≥0) where
  r_le := prodSeries.le_radius_of_eventually_le 0 <| eventually_atTop.2 ⟨3, fun k hk ↦ by
    have hk2 : k ≠ 2 := by omega
    simp [prodSeries, hk2]⟩
  r_pos := by simp
  hasSum {z} _ := by
    simp only [zero_add]
    rw [← prodSeries_two_apply (fun _ ↦ z)]
    exact hasSum_single 2 fun k hk ↦ by simp [prodSeries, hk]

theorem norm_prod_le_four {y : Fin 2 → ℂ} (hy : y ∈ ball (0 : Fin 2 → ℂ) 2) :
    ‖y 0 * y 1‖ ≤ 4 := by
  have hy' : ‖y‖ < 2 := by simpa using hy
  calc ‖y 0 * y 1‖ = ‖y 0‖ * ‖y 1‖ := norm_mul _ _
    _ ≤ ‖y‖ * ‖y‖ := mul_le_mul (norm_le_pi_norm y 0) (norm_le_pi_norm y 1)
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ 2 * 2 := mul_le_mul hy'.le hy'.le (norm_nonneg _) (by positivity)
    _ = 4 := by norm_num

theorem prodSeries_mvCoeff_one_one : prodSeries.mvCoeff ![1, 1] = 1 := by
  have hk : ∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i = 2 := by decide
  rw [prodSeries.mvCoeff_eq_sum hk]
  simp_rw [prodSeries_two_apply]
  rw [Finset.sum_eq_single (![0, 1] : Fin 2 → Fin 2)]
  · simp
  · intro a _ ha
    by_cases h0 : a 0 = 0
    · have h1 : a 1 ≠ 1 := fun h1 ↦ ha <| funext fun j ↦ by fin_cases j <;> assumption
      simp [Pi.single_apply, h1.symm]
    · simp [Pi.single_apply, Ne.symm h0]
  · intro hmem
    exfalso
    apply hmem
    simp only [mem_filter, mem_univ, true_and]
    decide

/-- At the boundary radius `ρ = 2`, `HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le` attains `4 ≤ 4`
for `prodSeries` at `α = ![1, 1]`, and `HasFPowerSeriesOnBall.norm_le_add_sum_mvCoeff` bounds
`‖z 0 * z 1‖` on `‖z‖ ≤ 1 < 2`. -/
example :
    (‖prodSeries.mvCoeff ![1, 1]‖ * (2 : ℝ) ^ (∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i) ≤ 4 ∧
      ‖prodSeries.mvCoeff ![1, 1]‖ * (2 : ℝ) ^ (∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i) = 4) ∧
    ‖(![1, 1] : Fin 2 → ℂ) 0 * (![1, 1] : Fin 2 → ℂ) 1‖ ≤
      (1 + (2 : ℕ)) * 4 * (1 / (2 : ℝ≥0)) ^ 2 +
        ∑ k ∈ range 2, ∑ α ∈ univ.piAntidiag k, ‖prodSeries.mvCoeff α‖ * (1 : ℝ) ^ k := by
  refine ⟨⟨hasFPowerSeriesOnBall_prod.norm_mvCoeff_mul_pow_le (fun _ hy ↦ norm_prod_le_four hy)
    ![1, 1] (by positivity) (by norm_num), ?_⟩, ?_⟩
  · rw [prodSeries_mvCoeff_one_one, show (∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i) = 2 by decide]
    norm_num
  · refine hasFPowerSeriesOnBall_prod.norm_le_add_sum_mvCoeff (fun _ hy ↦ norm_prod_le_four hy) 2
      (z := ![1, 1]) (r := 1) ?_ (by norm_num)
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ by fin_cases i <;> simp

/-! ### 4. Boundary counterexamples for `‖z‖ < R` and `1 ≤ T` -/

/-- `hz : ‖z‖ < R` cannot be weakened to `‖z‖ ≤ R` in
`HasFPowerSeriesOnBall.norm_sub_partialSum_le`: `f z = if ‖z‖ < 1 then 0 else 1` has formal power
series `0` on `ball 0 1` (`M = 0`), yet at `z = 1` the remainder norm is `1`. -/
example : ∃ (f : ℂ → ℂ) (z : ℂ),
    HasFPowerSeriesOnBall f (0 : FormalMultilinearSeries ℂ ℂ ℂ) 0 (1 : ℝ≥0) ∧
      (∀ y ∈ ball (0 : ℂ) (1 : ℝ≥0), ‖f y‖ ≤ 0) ∧ ‖z‖ ≤ (1 : ℝ≥0) ∧
      ¬(‖f z - (0 : FormalMultilinearSeries ℂ ℂ ℂ).partialSum 1 z‖ ≤
        (1 + (1 : ℕ)) * 0 * (‖z‖ / (1 : ℝ≥0)) ^ 1) := by
  classical
  refine ⟨fun z ↦ if ‖z‖ < 1 then 0 else 1, 1, ?_, ?_, by simp,
    by simp [FormalMultilinearSeries.partialSum]⟩
  · exact
      { r_le := by simp
        r_pos := by simp
        hasSum := fun {y} hy ↦ by
          rw [eball_coe] at hy
          have hy' : ‖y‖ < 1 := by simpa using hy
          simp [hy'] }
  · intro y hy
    have hy' : ‖y‖ < 1 := by simpa using hy
    simp [hy']

/-- `hT : 1 ≤ T` cannot be dropped at `T = 0` in
`TauCeti.isLittleO_sub_pow_sub_one_of_le_analyticOrderAt`: `g w = if w = 0 then 0 else 1` trivially
satisfies `(0 : ℕ∞) ≤ analyticOrderAt g 0`, yet `g w - g 0` is not `o(1)` as `w → 0`. -/
example : ∃ g : ℂ → ℂ, (0 : ℕ∞) ≤ analyticOrderAt g 0 ∧
    ¬((fun w ↦ g w - g 0) =o[𝓝 (0 : ℂ)] fun w ↦ ‖w - 0‖ ^ ((0 : ℕ) - 1)) := by
  classical
  refine ⟨fun w ↦ if w = 0 then 0 else 1, OrderBot.bot_le _, fun ho ↦ ?_⟩
  have hlim : Tendsto (fun w : ℂ ↦ (if w = 0 then (0 : ℂ) else 1) - 0) (𝓝[≠] 0) (𝓝 0) :=
    (Asymptotics.isLittleO_one_iff ℂ).1 (by simpa using ho) |>.mono_left nhdsWithin_le_nhds
  have hlim1 : Tendsto (fun w : ℂ ↦ (if w = 0 then (0 : ℂ) else 1) - 0) (𝓝[≠] 0) (𝓝 1) :=
    tendsto_const_nhds.congr' <| eventually_nhdsWithin_iff.2 <| .of_forall fun w (hw : w ≠ 0) ↦ by
      simp [hw]
  exact zero_ne_one (tendsto_nhds_unique hlim hlim1)

end TauCeti.PowerSeriesRemainderExample
