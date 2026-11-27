/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The entire-part series of the exponential integral

This file establishes convergence, termwise integration, regularity, monotonicity, and explicit
truncation bounds for the entire-part power series

```text
∑' n : ℕ, y ^ (n + 1) / ((n + 1) * (n + 1)!) = ∫ u in 0..y, (exp u - 1) / u.
```

Separating this API from `TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference` keeps matrix
exponential consumers of `Real.dslope_exp_eq_integral` and `Real.dslope_exp_pos` independent of
dominated convergence and monotonicity proofs.

## Main declarations

* `Real.summable_pow_div_mul_factorial`: absolute convergence for every `y : ℝ`.
* `Real.integral_dslope_exp_zero_eq_tsum` and `Real.integral_exp_sub_one_div_eq_tsum`: termwise
  integration identities on `[0, y]`.
* `Real.hasDerivAt_tsum_pow_div_mul_factorial`, `TauCeti.continuous_tsum_pow_div_mul_factorial`,
  `TauCeti.strictMono_tsum_pow_div_mul_factorial`, `TauCeti.tsum_pow_div_mul_factorial_mono`:
  derivative `dslope exp 0 y`, continuity, and strict monotonicity on `ℝ`.
* `TauCeti.sum_range_le_tsum_pow_div_mul_factorial` and
  `TauCeti.tsum_pow_div_mul_factorial_le_sum_range_add`: partial-sum lower bound for `y ≥ 0` and
  geometric-tail upper bound for `0 ≤ y < N + 2`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2.
-/

public section

open Filter MeasureTheory Set Real
open scoped Nat

namespace Real

/-- The series `∑_{n ≥ 1} y^n / (n * n!)` converges absolutely for every real `y`. -/
theorem summable_pow_div_mul_factorial (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hdom : Summable fun n : ℕ ↦ |y| ^ (n + 1) / ((n + 1)! : ℝ) :=
    (summable_nat_add_iff 1).mpr (summable_pow_div_factorial |y|)
  refine .of_norm_bounded hdom fun n ↦ ?_
  simp only [norm_eq_abs, abs_div, abs_pow, abs_mul, Nat.abs_cast]
  have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [abs_of_nonneg hpos]
  refine div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg y) _) (by positivity) ?_
  exact le_mul_of_one_le_left (by positivity) (by linarith)

/-- Termwise integration of `dslope exp 0` on `[0, y]` yields
`∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem integral_dslope_exp_zero_eq_tsum (y : ℝ) :
    (∫ u in (0 : ℝ)..y, dslope exp 0 u) =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hsum : HasSum (fun n : ℕ ↦ ∫ u in (0 : ℝ)..y, u ^ n / ((n + 1)! : ℝ))
      (∫ u in (0 : ℝ)..y, dslope exp 0 u) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ ↦ |y| ^ n / (n ! : ℝ))
      (fun n ↦ (by fun_prop : Continuous fun u : ℝ ↦ u ^ n / ((n + 1)! : ℝ)).aestronglyMeasurable)
      (fun n ↦ Eventually.of_forall fun u hu ↦ ?_)
      (Eventually.of_forall fun _ _ ↦ summable_pow_div_factorial |y|)
      intervalIntegrable_const
      (Eventually.of_forall fun u _ ↦ hasSum_dslope_exp_zero u)
    have habs : |u| ≤ |y| := by
      have hmem := uIoc_subset_uIcc hu
      rcases le_total 0 y with hy | hy
      · rw [uIcc_of_le hy] at hmem
        rw [abs_of_nonneg hmem.1, abs_of_nonneg hy]
        exact hmem.2
      · rw [uIcc_of_ge hy] at hmem
        rw [abs_of_nonpos hmem.2, abs_of_nonpos hy]
        linarith [hmem.1]
    simp only [norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    gcongr
    exact Nat.le_succ n
  rw [← hsum.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
    div_div, mul_comm]

/-- The entire part `∑_{n ≥ 1} y^n / (n * n!)` of the exponential integral equals
`∫ u in 0..y, (exp u - 1) / u`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    (∫ u in (0 : ℝ)..y, (exp u - 1) / u) =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [← integral_dslope_exp_zero_eq_tsum]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with u hu _
  exact (TauCeti.dslope_exp_zero_of_ne hu).symm

/-- The entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` has derivative `dslope exp 0 y` at every
real `y`. -/
theorem hasDerivAt_tsum_pow_div_mul_factorial (y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑' n : ℕ, t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (dslope exp 0 y) y := by
  have heq : (fun t : ℝ ↦ ∑' n : ℕ, t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) =
      fun t ↦ ∫ u in (0 : ℝ)..t, dslope exp 0 u :=
    funext fun t ↦ (integral_dslope_exp_zero_eq_tsum t).symm
  rw [heq]
  exact intervalIntegral.integral_hasDerivAt_right
    (TauCeti.continuous_dslope_exp_zero.intervalIntegrable 0 y)
    TauCeti.continuous_dslope_exp_zero.stronglyMeasurable.stronglyMeasurableAtFilter
    TauCeti.continuous_dslope_exp_zero.continuousAt

end Real

namespace TauCeti

/-- The entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_tsum_pow_div_mul_factorial :
    Continuous fun y : ℝ ↦ ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  continuous_iff_continuousAt.mpr fun y ↦ (hasDerivAt_tsum_pow_div_mul_factorial y).continuousAt

/-- The entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` is strictly increasing on all of `ℝ`. -/
theorem strictMono_tsum_pow_div_mul_factorial :
    StrictMono fun y : ℝ ↦ ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  strictMono_of_deriv_pos fun y ↦ by
    rw [(hasDerivAt_tsum_pow_div_mul_factorial y).deriv]
    exact dslope_exp_pos 0 y

/-- Monotonicity of the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` on `ℝ`. -/
theorem tsum_pow_div_mul_factorial_mono {x y : ℝ} (hxy : x ≤ y) :
    (∑' n : ℕ, x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  strictMono_tsum_pow_div_mul_factorial.monotone hxy

/-- Partial-sum lower bound for the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` when `y ≥ 0`. -/
theorem sum_range_le_tsum_pow_div_mul_factorial {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  (summable_pow_div_mul_factorial y).sum_le_tsum (Finset.range N) fun _ _ ↦ by positivity

private theorem pow_div_mul_factorial_succ_le {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    y ^ (n + 1 + 1) / ((((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 + 1)! : ℝ)) ≤
      (y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) * (y / (((n : ℝ) + 1) + 1)) := by
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  rw [← mul_div_mul_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have hy_nonneg : 0 ≤ y ^ (n + 1) * y * ((n + 1)! : ℝ) := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Geometric-tail upper bound for the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` when
`0 ≤ y < N + 2`. -/
theorem tsum_pow_div_mul_factorial_le_sum_range_add {y : ℝ} (hy : 0 ≤ y) {N : ℕ}
    (hN : y < (N : ℝ) + 2) :
    (∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) +
        (y ^ (N + 1) / (((N : ℝ) + 1) * ((N + 1)! : ℝ))) / (1 - y / ((N : ℝ) + 2)) := by
  let a : ℕ → ℝ := fun n ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))
  let r : ℝ := y / ((N : ℝ) + 2)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one (by positivity)).mpr hN
  have hsum := summable_pow_div_mul_factorial y
  rw [← hsum.sum_add_tsum_nat_add N]
  gcongr
  have hterm : ∀ k : ℕ, a (k + N) ≤ a N * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : a (k + 1 + N) ≤ a (k + N) * r := by
          have hr_le : y / (((k + N : ℕ) : ℝ) + 1 + 1) ≤ r := by
            refine div_le_div_of_nonneg_left hy (by positivity) ?_
            push_cast
            linarith
          rw [add_right_comm k 1 N]
          exact (pow_div_mul_factorial_succ_le hy (k + N)).trans
            (mul_le_mul_of_nonneg_left hr_le (by positivity))
        calc a (k + 1 + N)
            ≤ a (k + N) * r := hstep
          _ ≤ (a N * r ^ k) * r := mul_le_mul_of_nonneg_right ih hr0
          _ = a N * r ^ (k + 1) := by rw [pow_succ, mul_assoc]
  have hgeom : Summable fun k : ℕ ↦ a N * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (a N)
  calc (∑' k : ℕ, a (k + N))
      ≤ ∑' k : ℕ, a N * r ^ k := ((summable_nat_add_iff N).mpr hsum).tsum_le_tsum hterm hgeom
    _ = a N / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end TauCeti
