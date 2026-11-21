/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.MultiIndex
public import TauCeti.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.CPolynomialDef
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
  satisfies `‖p.mvCoeff ![1, 1]‖ * ρ ^ 2 ≤ 4` for every `0 ≤ ρ ≤ 2` (attained at `ρ = 2`).
-/

public section

open Filter Finset Metric
open scoped ENNReal NNReal Topology

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

/-- The `k`-th Taylor coefficient of `sqSeries` is `1` for `k = 2` and `0` otherwise. -/
@[simp]
theorem sqSeries_coeff (k : ℕ) : sqSeries.coeff k = if k = 2 then 1 else 0 := by
  simp [sqSeries, Pi.single_apply]

/-- All terms of `sqSeries` outside degree `2` vanish. -/
@[simp]
theorem sqSeries_of_ne {k : ℕ} (hk : k ≠ 2) : sqSeries k = 0 := by
  simp [sqSeries, hk]

/-- `sqSeries` represents `z ↦ z ^ 2` on `Metric.ball 0 2`. -/
theorem hasFPowerSeriesOnBall_sqSeries :
    HasFPowerSeriesOnBall (fun z : ℂ ↦ z ^ 2) sqSeries 0 (2 : ℝ≥0) :=
  (HasFiniteFPowerSeriesOnBall.mk' (n := 3)
    (fun _ hm ↦ sqSeries_of_ne (by omega))
    (by simp)
    (fun y _ ↦ by simp [sq])).toHasFPowerSeriesOnBall

-- Exact remainder norms `1, 1, 0` at `T = 0, 2, 3`.
example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 0 1‖ = 1 := by
  simp [FormalMultilinearSeries.partialSum]

example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 2 1‖ = 1 := by
  norm_num [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]

example : ‖((1 : ℂ) ^ 2) - sqSeries.partialSum 3 1‖ = 0 := by
  norm_num [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]

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
private noncomputable def prodCoordMap : ContinuousMultilinearMap ℂ (fun _ : Fin 2 ↦ Fin 2 → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ 2 ℂ).compContinuousLinearMap
    (fun j : Fin 2 ↦ ContinuousLinearMap.proj (R := ℂ) j)

/-- The formal multilinear series on `Fin 2 → ℂ` whose only nonzero term is `(u, v) ↦ u 0 * v 1`
in degree `2`, representing `z ↦ z 0 * z 1`. -/
noncomputable def prodCoordSeries : FormalMultilinearSeries ℂ (Fin 2 → ℂ) ℂ :=
  fun k ↦ if h : k = 2 then h ▸ prodCoordMap else 0

/-- All terms of `prodCoordSeries` outside degree `2` vanish. -/
@[simp]
theorem prodCoordSeries_of_ne {k : ℕ} (hk : k ≠ 2) : prodCoordSeries k = 0 := by
  simp [prodCoordSeries, hk]

/-- In degree `2`, `prodCoordSeries` evaluates `(u, v)` to `u 0 * v 1`. -/
@[simp]
theorem prodCoordSeries_two_apply (v : Fin 2 → Fin 2 → ℂ) :
    prodCoordSeries 2 v = v 0 0 * v 1 1 := by
  simp [prodCoordSeries, prodCoordMap]

/-- The `![1, 1]` multi-index coefficient of `prodCoordSeries` is `1`. -/
@[simp]
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
  simp

/-- `prodCoordSeries` represents `z ↦ z 0 * z 1` on `Metric.ball 0 2`. -/
theorem hasFPowerSeriesOnBall_prodCoordSeries :
    HasFPowerSeriesOnBall (fun z : Fin 2 → ℂ ↦ z 0 * z 1) prodCoordSeries 0 (2 : ℝ≥0) :=
  (HasFiniteFPowerSeriesOnBall.mk' (n := 3)
    (fun _ hm ↦ prodCoordSeries_of_ne (by omega))
    (by simp)
    (fun y _ ↦ by simp [Finset.sum_range_succ])).toHasFPowerSeriesOnBall

private theorem norm_prodCoord_le_four {y : Fin 2 → ℂ} (hy : y ∈ ball (0 : Fin 2 → ℂ) 2) :
    ‖y 0 * y 1‖ ≤ 4 := by
  have hy2 : ‖y‖ < 2 := by simpa using hy
  have h0 : ‖y 0‖ ≤ 2 := (norm_le_pi_norm y 0).trans hy2.le
  have h1 : ‖y 1‖ ≤ 2 := (norm_le_pi_norm y 1).trans hy2.le
  calc ‖y 0 * y 1‖ = ‖y 0‖ * ‖y 1‖ := norm_mul _ _
    _ ≤ 2 * 2 := mul_le_mul h0 h1 (norm_nonneg _) (by norm_num)
    _ = 4 := by norm_num

-- Multi-index Cauchy inequality on `Fin 2 → ℂ`: `‖mvCoeff ![1, 1]‖ * ρ ^ 2 ≤ 4` for `0 ≤ ρ ≤ 2`.
example {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 2) :
    ‖prodCoordSeries.mvCoeff ![1, 1]‖ * ρ ^ 2 ≤ 4 := by
  simpa using hasFPowerSeriesOnBall_prodCoordSeries.norm_mvCoeff_mul_pow_le
    (fun _ hy ↦ norm_prodCoord_le_four (by simpa using hy)) ![1, 1] hρ0 (by simpa using hρ)

-- Multi-index Cauchy inequality at the boundary radius `ρ = 2` attains `4 = 4`.
example :
    ‖prodCoordSeries.mvCoeff ![1, 1]‖ * (2 : ℝ) ^ (∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i) ≤ 4 ∧
      ‖prodCoordSeries.mvCoeff ![1, 1]‖ * (2 : ℝ) ^ (∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i) = 4 := by
  refine ⟨hasFPowerSeriesOnBall_prodCoordSeries.norm_mvCoeff_mul_pow_le
    (fun _ hy ↦ norm_prodCoord_le_four (by simpa using hy)) ![1, 1] (by positivity)
    (by norm_num), ?_⟩
  have hdeg : (∑ i : Fin 2, (![1, 1] : Fin 2 → ℕ) i) = 2 := by decide
  rw [mvCoeff_prodCoordSeries_one_one, hdeg]
  norm_num

-- Unequal-polyradii Cauchy inequality on `Fin 2 → ℂ` at `ρ = ![1, 2]`.
example :
    ‖prodCoordSeries.mvCoeff ![1, 1]‖ *
      ∏ i : Fin 2, (![1, 2] : Fin 2 → ℝ) i ^ (![1, 1] : Fin 2 → ℕ) i ≤ 4 :=
  hasFPowerSeriesOnBall_prodCoordSeries.norm_mvCoeff_mul_prod_pow_le
    (fun _ hy ↦ norm_prodCoord_le_four (by simpa using hy)) ![1, 1]
    (fun i ↦ by fin_cases i <;> norm_num) (fun i ↦ by fin_cases i <;> norm_num)

-- Multi-index truncated Taylor bound at `T = 2` on `Fin 2 → ℂ`, `R = 2`, `r = 1`.
example {z : Fin 2 → ℂ} (hz : ‖z‖ ≤ 1) :
    ‖z 0 * z 1‖ ≤ (1 + (2 : ℕ)) * 4 * ((1 : ℝ) / 2) ^ 2 +
      ∑ k ∈ range 2, ∑ α ∈ univ.piAntidiag k, ‖prodCoordSeries.mvCoeff α‖ * (1 : ℝ) ^ k :=
  hasFPowerSeriesOnBall_prodCoordSeries.norm_le_add_sum_mvCoeff
    (fun _ hy ↦ norm_prodCoord_le_four (by simpa using hy)) 2 hz (by norm_num)

/-! ### Boundary counterexamples for `‖z‖ < R` and `1 ≤ T` -/

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

end TauCeti.TaylorRemainderExample
