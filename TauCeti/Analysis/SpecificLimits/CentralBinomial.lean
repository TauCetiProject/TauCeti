/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summability of central-binomial series

For real `q`, the series with terms `Nat.centralBinom n * q ^ n` is summable
exactly when `|q| < 1 / 4`. At the boundary, the elementary lower bound on central
binomial coefficients compares this series with the harmonic series; no asymptotic
formula is needed.

The extended nonnegative sum detects the same boundary without the convention that
an unsummable real series has sum zero. In particular, for a nearest-neighbor walk
with right-step probability `p`, the sum of the even-time return probabilities
`Nat.centralBinom n * (p * (1 - p)) ^ n` is infinite exactly at `p = 1 / 2`.
This is the numerical input to the Green-function recurrence criterion.

The random-walk application follows J. R. Norris, *Markov Chains* (1997), §1.6.
The estimates used here are Mathlib's `Nat.centralBinom_le_four_pow` and
`Nat.four_pow_le_two_mul_self_mul_centralBinom`.
-/

public section

open scoped NNReal ENNReal

namespace Real

/-- The central-binomial series diverges at its radius of convergence. -/
theorem not_summable_centralBinom_div_four_pow :
    ¬ Summable (fun n : ℕ => (n.centralBinom : ℝ) / 4 ^ n) := by
  intro h
  apply not_summable_natCast_inv
  refine (h.mul_left 2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num
  have hbound : (4 : ℝ) ^ n ≤ 2 * n * (n.centralBinom : ℝ) := by
    exact_mod_cast Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0 : ℝ) < 4 ^ n),
    inv_mul_le_iff₀ hn']
  nlinarith

/-- A real central-binomial power series is summable exactly inside its
radius of convergence; both boundary points are excluded. -/
theorem summable_centralBinom_mul_pow_iff {q : ℝ} :
    Summable (fun n : ℕ => (n.centralBinom : ℝ) * q ^ n) ↔ |q| < 1 / 4 := by
  have key (q : ℝ) (hq : 0 ≤ q) :
      Summable (fun n : ℕ => (n.centralBinom : ℝ) * q ^ n) ↔ q < 1 / 4 := by
    constructor
    · intro h
      by_contra hlt
      have hq' : 1 / 4 ≤ q := le_of_not_gt hlt
      apply not_summable_centralBinom_div_four_pow
      refine h.of_nonneg_of_le (fun n => by positivity) fun n => ?_
      rw [div_eq_mul_inv, ← inv_pow]
      gcongr
      simpa using hq'
    · intro hq'
      have hgeo : Summable (fun n : ℕ => (4 * q) ^ n) :=
        summable_geometric_of_lt_one (by positivity) (by linarith)
      refine hgeo.of_nonneg_of_le (fun n => by positivity) fun n => ?_
      rw [mul_pow]
      gcongr
      exact_mod_cast Nat.centralBinom_le_four_pow n
  rw [← summable_abs_iff]
  simpa only [abs_mul, abs_pow, Nat.abs_cast] using key |q| (abs_nonneg q)

end Real

namespace NNReal

/-- The extended central-binomial series is infinite exactly at and beyond the
radius of convergence. This statement also includes `q = 0`. -/
theorem tsum_centralBinom_mul_pow_eq_top_iff (q : ℝ≥0) :
    (∑' n : ℕ, (n.centralBinom : ℝ≥0∞) * (q : ℝ≥0∞) ^ n) = ∞ ↔ 1 / 4 ≤ q := by
  rw [← NNReal.coe_le_coe]
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_natCast,
    NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
    Real.summable_centralBinom_mul_pow_iff, abs_of_nonneg q.coe_nonneg, not_lt,
    NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    (ENNReal.tsum_coe_eq_top_iff_not_summable_coe
      (f := fun n : ℕ => (n.centralBinom : ℝ≥0) * q ^ n))

/-- The even-time return series of a nearest-neighbor walk is infinite exactly
for the symmetric step law. Deterministic steps (`p = 0` or `p = 1`) are included. -/
theorem tsum_centralBinom_mul_mul_one_sub_pow_eq_top_iff (p : ℝ≥0) (hp : p ≤ 1) :
    (∑' n : ℕ, (n.centralBinom : ℝ≥0∞) * ((p * (1 - p) : ℝ≥0) : ℝ≥0∞) ^ n) = ∞ ↔
      p = 1 / 2 := by
  rw [tsum_centralBinom_mul_pow_eq_top_iff]
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hp]
  constructor
  · intro h
    have h' : (1 : ℝ) / 4 ≤ (p : ℝ) * (1 - p) := by exact_mod_cast h
    have heq : (p : ℝ) = 1 / 2 := by nlinarith [sq_nonneg ((p : ℝ) - 1 / 2)]
    exact NNReal.coe_injective (by simpa using heq)
  · rintro rfl
    norm_num

end NNReal
