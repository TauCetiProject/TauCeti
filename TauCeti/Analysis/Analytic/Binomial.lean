/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Binomial

/-!
# Convergence of multichoose power series

This file determines the exact unconditional summability domain of the power series with
generalized multichoose coefficients and positive real parameter.  The result applies to both real
and complex arguments.  These results supply the analytic criterion used to determine the exact
integrability domain of the negative-binomial probability-generating function.

## Main declarations

* `TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one` — the multichoose binomial
  series on the open unit interval.
* `TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one` — the complex-valued
  multichoose binomial series on the open unit disk.
* `TauCeti.summable_multichoose_mul_geometric_iff_norm_lt_one` — exact summability of
  `∑ n, multichoose r n * q ^ n` for `0 < r`.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace TauCeti

/-- The generalized multichoose power series sums to `(1 - x)⁻ʳ` when `|x| < 1`. -/
theorem hasSum_multichoose_mul_geometric_of_abs_lt_one {r x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.multichoose r n * x ^ n) (1 / (1 - x) ^ r) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one,
      Real.norm_eq_abs]
  simpa [Ring.multichoose_eq, mul_comm] using
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum_sub hmem

/-- The generalized multichoose power series sums to `(1 - z)⁻ʳ` throughout the complex open
unit disk. -/
theorem hasSum_multichoose_mul_geometric_complex_of_norm_lt_one {r z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => Ring.multichoose r n * z ^ n) (1 / (1 - z) ^ r) := by
  have hmem : z ∈ Metric.eball (0 : ℂ) 1 := by
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  simpa [Ring.multichoose_eq, mul_comm] using
    (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero r).hasSum_sub hmem

/-- For positive real `r`, the generalized multichoose power series is unconditionally summable
at a real or complex argument `q` exactly when `q` lies in the open unit ball. -/
@[simp]
theorem summable_multichoose_mul_geometric_iff_norm_lt_one
    {𝕂 : Type*} [RCLike 𝕂] {r : ℝ} {q : 𝕂} (hr : 0 < r) :
    Summable (fun n : ℕ => ((Ring.multichoose r n : ℝ) : 𝕂) * q ^ n) ↔ ‖q‖ < 1 := by
  have hcoeff_pos (n : ℕ) : 0 < Ring.multichoose r n := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    exact pos_of_mul_pos_right (h ▸ ascPochhammer_pos n r hr) (by positivity)
  -- At the boundary point `1` the coefficients themselves are not summable: their sum would
  -- bound `(1 - x)⁻ʳ` on `[0, 1)`, which tends to infinity as `x → 1⁻`.
  have hnot : ¬ Summable (fun n : ℕ => Ring.multichoose r n) := by
    intro hs
    have hsub : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
      simpa using (continuous_sub_left (1 : ℝ)).continuousWithinAt.tendsto_nhdsWithin
        (s := Iio 1) (t := Ioi 0) (x := 1) fun x hx => sub_pos.2 hx
    have htop : Tendsto (fun x : ℝ => 1 / (1 - x) ^ r) (𝓝[<] 1) atTop := by
      refine ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.2 hr)).comp hsub).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [Real.rpow_neg (sub_nonneg.2 (le_of_lt hx))]
    obtain ⟨x, hlt, hx⟩ := ((htop.eventually_gt_atTop (∑' n, Ring.multichoose r n)).and
      (Ioo_mem_nhdsLT zero_lt_one)).exists
    refine hlt.not_ge (hasSum_le (fun n => ?_) (hasSum_multichoose_mul_geometric_of_abs_lt_one
      (abs_lt.2 ⟨by linarith [hx.1], hx.2⟩)) hs.hasSum)
    exact mul_le_of_le_one_right (hcoeff_pos n).le (pow_le_one₀ hx.1.le hx.2.le)
  rw [← summable_norm_iff]
  simp_rw [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos (hcoeff_pos _)]
  refine ⟨fun hs => not_le.1 fun hq => hnot (hs.of_nonneg_of_le (fun n => (hcoeff_pos n).le)
    fun n => le_mul_of_one_le_right (hcoeff_pos n).le (one_le_pow₀ hq)), fun hq => ?_⟩
  exact (hasSum_multichoose_mul_geometric_of_abs_lt_one (by simpa using hq)).summable

end TauCeti

end
