/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.MultiIndex
public import TauCeti.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Tactic.FinCases

/-!
# Worked examples for Schwarz's lemma, Cauchy's inequality and Taylor remainders

Concrete checks of the constants and normalisations in
`Complex.norm_le_mul_div_pow_of_le_analyticOrderAt`,
`HasFPowerSeriesOnBall.norm_sub_partialSum_le`, `HasFPowerSeriesOnBall.norm_mvCoeff_mul_pow_le`, and
`HasFPowerSeriesOnBall.norm_le_add_sum_mvCoeff`:

* For `g w = w ^ 2` on `Metric.ball (0 : ℂ) 2` (`M = 4`, `T = 2`), at `w = 1` both `‖g 1‖` and
  the Schwarz bound `4 * (‖(1 : ℂ) - 0‖ / 2) ^ 2` equal `1`.
* For `F z = z ^ 2` on `Metric.ball (0 : ℂ) 2` (`R = 2`, `M = 4`) at `z = 1`, the Taylor
  remainders at orders `T = 0, 2, 3` have norms `1, 1, 0` while `(1 + T) * 4 * (1 / 2) ^ T`
  evaluates to `4, 3, 2`.
* On `Fin 2 → ℂ`, the bilinear monomial `F z = z 0 * z 1`, represented by the unsymmetrised
  series with single nonzero term `p 2 (u, v) = u 0 * v 1`, has `p.mvCoeff ![1, 1] = 1` and
  satisfies `‖p.mvCoeff ![1, 1]‖ * ρ ^ 2 ≤ 4` for every `0 ≤ ρ < 2` (tight as `ρ → 2`).
-/

public section

open Finset Metric
open scoped ENNReal NNReal

namespace TauCeti.TaylorRemainderExample

/-! ### One-variable Schwarz lemma at `g w = w ^ 2` -/

private theorem sq_differentiableOn_ball :
    DifferentiableOn ℂ (fun w : ℂ ↦ w ^ 2) (ball 0 2) :=
  (differentiable_id.pow 2).differentiableOn

private theorem sq_norm_le_four {w : ℂ} (hw : w ∈ ball (0 : ℂ) 2) : ‖w ^ 2‖ ≤ 4 := by
  have hw2 : ‖w‖ < 2 := by simpa using hw
  calc ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow w 2
    _ ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hw2.le 2
    _ = 4 := by norm_num

private theorem two_le_analyticOrderAt_sq :
    (2 : ℕ∞) ≤ analyticOrderAt (fun w : ℂ ↦ w ^ 2) 0 := by
  have h : analyticOrderAt (fun w : ℂ ↦ (w - 0) ^ 2) 0 = 2 := analyticOrderAt_centeredMonomial
  simpa using h.ge

-- At `w = 1`, `g w = w ^ 2` attains the Schwarz bound `4 * (1 / 2) ^ 2 = 1`.
example : ‖((1 : ℂ) ^ 2)‖ = 1 ∧ (4 : ℝ) * (‖(1 : ℂ) - 0‖ / 2) ^ 2 = 1 := by
  norm_num

example : ‖((1 : ℂ) ^ 2)‖ ≤ 4 * (‖(1 : ℂ) - 0‖ / 2) ^ 2 :=
  Complex.norm_le_mul_div_pow_of_le_analyticOrderAt sq_differentiableOn_ball
    (fun _ hw ↦ sq_norm_le_four hw) two_le_analyticOrderAt_sq (by norm_num)

/-! ### Truncated Taylor remainders for `F z = z ^ 2` at `R = 2`, `M = 4`, `z = 1` -/

/-- The scalar power series of `z ↦ z ^ 2` about `0`. -/
noncomputable def sqSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (Pi.single 2 1)

theorem hasFPowerSeriesOnBall_sqSeries :
    HasFPowerSeriesOnBall (fun z : ℂ ↦ z ^ 2) sqSeries 0 (2 : ℝ≥0) where
  r_le := by
    refine FormalMultilinearSeries.le_radius_of_summable _ (r := 2) ?_
    refine summable_of_ne_finset_zero (s := {2}) fun n hn ↦ ?_
    have hn2 : n ≠ 2 := by simpa using hn
    simp [sqSeries, hn2]
  r_pos := by simp
  hasSum := fun {y} _ ↦ by
    have h2 : sqSeries 2 (fun _ ↦ y) = (0 + y) ^ 2 := by simp [sqSeries]
    rw [← h2]
    exact hasSum_single 2 fun n hn ↦ by simp [sqSeries, Pi.single_eq_of_ne hn]

-- Exact remainder norms `1, 1, 0` at `T = 0, 2, 3`.
example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 0 1‖ = 1 := by
  simp [FormalMultilinearSeries.partialSum]

example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 2 1‖ = 1 := by
  norm_num [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, sqSeries]

example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 3 1‖ = 0 := by
  norm_num [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, sqSeries]

-- Corresponding remainder bounds `4, 3, 2` from `HasFPowerSeriesOnBall.norm_sub_partialSum_le`.
example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 0 1‖ ≤ 4 := by
  refine (hasFPowerSeriesOnBall_sqSeries.norm_sub_partialSum_le
    (fun _ hy ↦ sq_norm_le_four (by simpa using hy)) 0 (z := 1) (by norm_num)).trans_eq ?_
  norm_num

example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 2 1‖ ≤ 3 := by
  refine (hasFPowerSeriesOnBall_sqSeries.norm_sub_partialSum_le
    (fun _ hy ↦ sq_norm_le_four (by simpa using hy)) 2 (z := 1) (by norm_num)).trans_eq ?_
  norm_num

example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 3 1‖ ≤ 2 := by
  refine (hasFPowerSeriesOnBall_sqSeries.norm_sub_partialSum_le
    (fun _ hy ↦ sq_norm_le_four (by simpa using hy)) 3 (z := 1) (by norm_num)).trans_eq ?_
  norm_num

/-! ### Multi-index Cauchy inequality on `Fin 2 → ℂ` for `z 0 * z 1` -/

/-- The unsymmetrised bilinear map `(u, v) ↦ u 0 * v 1` on `Fin 2 → ℂ`. -/
noncomputable def prodCoordMap : ContinuousMultilinearMap ℂ (fun _ : Fin 2 ↦ Fin 2 → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ 2 ℂ).compContinuousLinearMap
    (fun j : Fin 2 ↦ ContinuousLinearMap.proj (R := ℂ) j)

/-- The formal multilinear series on `Fin 2 → ℂ` whose only nonzero term is `prodCoordMap` in
degree `2`, representing `z ↦ z 0 * z 1`. -/
noncomputable def prodCoordSeries : FormalMultilinearSeries ℂ (Fin 2 → ℂ) ℂ :=
  fun k ↦ if h : k = 2 then h ▸ prodCoordMap else 0

theorem mvCoeff_prodCoordSeries_one_one :
    prodCoordSeries.mvCoeff ![1, 1] = 1 := by
  rw [FormalMultilinearSeries.mvCoeff_eq_sum prodCoordSeries (k := 2) (by decide)]
  have hmem (a : Fin 2 → Fin 2) :
      (∀ i : Fin 2, Fintype.card {j : Fin 2 // a j = i} = (![1, 1] : Fin 2 → ℕ) i) ↔
        a = ![0, 1] ∨ a = ![1, 0] := by
    have ha : a = ![a 0, a 1] := by ext j; fin_cases j <;> rfl
    rw [ha]
    generalize a 0 = x, a 1 = y
    fin_cases x <;> fin_cases y <;> decide
  have hfilt : (univ.filter fun a : Fin 2 → Fin 2 ↦
      ∀ i, Fintype.card {j // a j = i} = (![1, 1] : Fin 2 → ℕ) i) = {![0, 1], ![1, 0]} := by
    ext a
    simp [hmem]
  refine (Finset.sum_congr hfilt fun _ _ ↦ rfl).trans ?_
  rw [Finset.sum_pair (by decide)]
  simp [prodCoordSeries, prodCoordMap]

theorem hasFPowerSeriesOnBall_prodCoordSeries :
    HasFPowerSeriesOnBall (fun z : Fin 2 → ℂ ↦ z 0 * z 1) prodCoordSeries 0 (2 : ℝ≥0) where
  r_le := by
    refine FormalMultilinearSeries.le_radius_of_summable _ (r := 2) ?_
    refine summable_of_ne_finset_zero (s := {2}) fun n hn ↦ ?_
    have hn2 : n ≠ 2 := by simpa using hn
    simp [prodCoordSeries, hn2]
  r_pos := by simp
  hasSum := fun {y} _ ↦ by
    have h2 : prodCoordSeries 2 (fun _ ↦ y) = (0 + y) 0 * (0 + y) 1 := by
      simp [prodCoordSeries, prodCoordMap]
    rw [← h2]
    exact hasSum_single 2 fun n hn ↦ by simp [prodCoordSeries, hn]

private theorem norm_prodCoord_le_four {y : Fin 2 → ℂ} (hy : y ∈ ball (0 : Fin 2 → ℂ) 2) :
    ‖y 0 * y 1‖ ≤ 4 := by
  have hy2 : ‖y‖ < 2 := by simpa using hy
  have h0 : ‖y 0‖ ≤ 2 := (norm_le_pi_norm y 0).trans hy2.le
  have h1 : ‖y 1‖ ≤ 2 := (norm_le_pi_norm y 1).trans hy2.le
  calc ‖y 0 * y 1‖ = ‖y 0‖ * ‖y 1‖ := norm_mul _ _
    _ ≤ 2 * 2 := mul_le_mul h0 h1 (norm_nonneg _) (by norm_num)
    _ = 4 := by norm_num

-- Multi-index Cauchy inequality on `Fin 2 → ℂ`: `‖mvCoeff ![1, 1]‖ * ρ ^ 2 ≤ 4` for `0 ≤ ρ < 2`.
example {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 2) :
    ‖prodCoordSeries.mvCoeff ![1, 1]‖ * ρ ^ 2 ≤ 4 := by
  simpa using hasFPowerSeriesOnBall_prodCoordSeries.norm_mvCoeff_mul_pow_le
    (fun _ hy ↦ norm_prodCoord_le_four (by simpa using hy)) ![1, 1] hρ0 (by simpa using hρ)

-- Multi-index truncated Taylor bound at `T = 2` on `Fin 2 → ℂ`, `R = 2`, `r = 1`.
example {z : Fin 2 → ℂ} (hz : ‖z‖ ≤ 1) :
    ‖z 0 * z 1‖ ≤ (1 + (2 : ℕ)) * 4 * ((1 : ℝ) / 2) ^ 2 +
      ∑ k ∈ range 2, ∑ α ∈ univ.piAntidiag k, ‖prodCoordSeries.mvCoeff α‖ * (1 : ℝ) ^ k :=
  hasFPowerSeriesOnBall_prodCoordSeries.norm_le_add_sum_mvCoeff
    (fun _ hy ↦ norm_prodCoord_le_four (by simpa using hy)) 2 hz (by norm_num)

end TauCeti.TaylorRemainderExample
