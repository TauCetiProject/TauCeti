/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A large-deviation bound for the binomial law

An upper tail beginning at least six times the mean has mass at most `2⁻ᵏ`,
where `k` is the first index in the tail. This is useful when taking a union
bound over many windows of Bernoulli trials.
-/

public section

open MeasureTheory ProbabilityTheory Set Real

namespace TauCeti.Probability

/-- The binomial upper tail at `k` has mass at most `2⁻ᵏ` if the mean is at most `k / 6`. -/
theorem measureReal_binomial_Ici_le_half_pow {n k : ℕ} (p : unitInterval)
    (hk : 6 * (n : ℝ) * (p : ℝ) ≤ k) :
    (binomial n p).real (Ici k) ≤ (1 / 2 : ℝ) ^ k := by
  have ht : 0 ≤ log 4 := log_nonneg (by norm_num)
  have hInt := integrable_map_cast_binomial (n := n) (p := p)
    (fun x : ℝ ↦ exp (log 4 * id x))
  have hbound := measure_ge_le_exp_mul_mgf (μ := Bin(ℝ, n, p)) (X := id) (k : ℝ) ht hInt
  have hpre : (fun j : ℕ ↦ (j : ℝ)) ⁻¹' Ici (k : ℝ) = Ici k := by
    ext j
    simp
  rw [show {x : ℝ | (k : ℝ) ≤ id x} = Ici (k : ℝ) from rfl,
    Measure.real, Measure.map_apply (by fun_prop) measurableSet_Ici, hpre,
    mgf_id_map_cast_binomial, exp_log (by norm_num : (0 : ℝ) < 4)] at hbound
  have hbase : 1 - (p : ℝ) + (p : ℝ) * 4 ≤ exp (3 * (p : ℝ)) := by
    simpa only [show 1 - (p : ℝ) + (p : ℝ) * 4 = 3 * (p : ℝ) + 1 by ring]
      using add_one_le_exp (3 * (p : ℝ))
  have hlog : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  calc
    _ ≤ exp (-log 4 * k) * (1 - (p : ℝ) + (p : ℝ) * 4) ^ n := hbound
    _ ≤ exp (-log 4 * k) * exp (3 * (p : ℝ)) ^ n := by
      gcongr
      linarith [p.property.1]
    _ ≤ exp (-log 4 * k) * exp (log 2 * k) := by
      rw [← exp_natCast_mul]
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (Nat.cast_nonneg k)]
    _ = (1 / 2 : ℝ) ^ k := by
      rw [← exp_add, ← exp_log (by norm_num : (0 : ℝ) < 1 / 2), ← exp_natCast_mul]
      congr 1
      rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul (by norm_num) (by norm_num),
        one_div, log_inv]
      ring

end TauCeti.Probability
