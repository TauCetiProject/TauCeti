/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
import TauCeti.NumberTheory.Bernoulli.Values

/-!
# Bernoulli polynomials and Bernoulli functions

Mathlib's `bernoulliFun` is the real-variable Bernoulli polynomial. This file records how it
relates to the Bernoulli polynomial over `ℚ`, together with the sign and extremality properties of
the even Bernoulli functions `B_{2k}(x)` on `[0, 1]`, deduced from their cosine Fourier series
(`hasSum_one_div_nat_pow_mul_cos` and `hasSum_zeta_nat`) and
`TauCeti.neg_one_pow_mul_bernoulli_two_mul_pos`.

## Main results

* `TauCeti.bernoulliFun_ratCast`: `bernoulliFun` at a rational point is the Bernoulli polynomial
  over `ℚ` evaluated there, mapped into `ℝ`.
* `TauCeti.hasSum_one_sub_cos_div_nat_pow`: exact cosine Fourier series for `B_{2k} - B_{2k}(x)`
  on `[0, 1]`.
* `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg`: on `[0, 1]`,
  `B_{2k} - B_{2k}(x)` has the sign `(-1)^(k+1)` of `B_{2k}` (or vanishes).
* `TauCeti.neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_pos`:
  `(-1) ^ (k + 1) * (B_{2k} - B_{2k}(x))` is strictly positive on `(0, 1)` for `k ≥ 1`.
* `TauCeti.abs_bernoulliFun_even_le`: for all `k` and `x ∈ [0, 1]`, `|B_{2k}(x)| ≤ |B_{2k}|`.
* `TauCeti.neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg`,
  `TauCeti.abs_bernoulliFun_even_fract_le`: the corresponding periodic statements at `Int.fract u`.
-/

public section

open scoped Nat Real

namespace TauCeti

/-- `bernoulliFun` at a rational point is the Bernoulli polynomial over `ℚ` evaluated there,
mapped into `ℝ`. -/
theorem bernoulliFun_ratCast (k : ℕ) (x : ℚ) :
    bernoulliFun k (x : ℝ) = (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) := by
  simp only [bernoulliFun, Polynomial.eval_map, ← map_ratCast (algebraMap ℚ ℝ),
    Polynomial.eval₂_at_apply]
  norm_cast

private theorem hasSum_one_div_nat_pow_bernoulli {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        (bernoulli (2 * k) : ℝ)) := by
  convert hasSum_zeta_nat hk using 1
  have h2 : (2 : ℝ) ^ (2 * k - 1) = (2 : ℝ) ^ (2 * k) / 2 := by
    rw [eq_div_iff (two_ne_zero' ℝ), ← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [h2, mul_pow]
  ring

private theorem hasSum_cos_div_nat_pow_bernoulliFun {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        bernoulliFun (2 * k) x) := by
  convert hasSum_one_div_nat_pow_mul_cos hk hx using 1
  rw [← bernoulliFun]
  ring

/-- Exact cosine Fourier series for the Bernoulli endpoint difference `B_{2k} - B_{2k}(x)` on
`[0, 1]`: for `k ≠ 0` and `x ∈ [0, 1]`,
`∑' n : ℕ, (1 - cos (2π n x)) / n^{2k} = (-1)^{k+1} ((2π)^{2k} / (2 (2k)!)) (B_{2k} - B_{2k}(x))`.
-/
theorem hasSum_one_sub_cos_div_nat_pow {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ (1 - Real.cos (2 * π * n * x)) / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)) := by
  convert (hasSum_one_div_nat_pow_bernoulli hk).sub (hasSum_cos_div_nat_pow_bernoulliFun hk hx)
    using 1
  · ext n; ring
  · ring

/-- On `[0, 1]` the even Bernoulli polynomial lies on one side of its value at `0`:
`(-1)^(k+1) (B_{2k} - B_{2k}(x)) ≥ 0`, so `B_{2k} - B_{2k}(x)` has the sign of `B_{2k}`. -/
theorem neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (-1) ^ (k + 1) * (bernoulli (2 * k) - bernoulliFun (2 * k) x) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hx' := hasSum_one_div_nat_pow_mul_cos hk hx
  have h0 := hasSum_one_div_nat_pow_mul_cos hk (Set.left_mem_Icc.mpr zero_le_one)
  rw [← bernoulliFun] at hx' h0
  rw [bernoulliFun_eval_zero] at h0
  -- Termwise, `cos (2π n x) / n^(2k) ≤ 1 / n^(2k)`.
  have hle := hasSum_le (fun n => ?_) hx' h0
  · have hC : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) / 2 / (2 * k).factorial := by positivity
    have : 0 ≤ (2 * Real.pi) ^ (2 * k) / 2 / (2 * k).factorial *
        ((-1) ^ (k + 1) * (bernoulli (2 * k) - bernoulliFun (2 * k) x)) := by
      convert sub_nonneg.mpr hle using 1
      ring
    exact nonneg_of_mul_nonneg_right this hC
  · simp only [mul_zero, Real.cos_zero, mul_one]
    exact mul_le_of_le_one_right (by positivity) (Real.cos_le_one _)

/-- For `k ≥ 1` and `x ∈ (0, 1)`, the difference `B_{2k} - B_{2k}(x)` strictly has the sign of
`B_{2k}`: `0 < (-1) ^ (k + 1) * (B_{2k} - B_{2k}(x))`. -/
theorem neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_pos {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := by
  have hsum := hasSum_one_sub_cos_div_nat_pow hk (Set.Ioo_subset_Icc_self hx)
  have hcos : Real.cos (2 * π * x) < 1 := by
    have hx0 : 0 < x := hx.1
    refine (Real.cos_le_one _).lt_of_ne fun h ↦ ?_
    have hzero := (Real.cos_eq_one_iff_of_lt_of_lt
      (by nlinarith [Real.pi_pos, hx.1]) (by nlinarith [Real.pi_pos, hx.2])).mp h
    exact (by positivity : (0 : ℝ) < 2 * π * x).ne' hzero
  have hgt : 0 < ∑' n : ℕ, (1 - Real.cos (2 * π * n * x)) / (n : ℝ) ^ (2 * k) :=
    hsum.summable.tsum_pos
      (fun _ ↦ div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by positivity))
      1 (by simpa using hcos)
  rw [hsum.tsum_eq] at hgt
  exact pos_of_mul_pos_right (by linarith :
      0 < ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)))
    (by positivity)

/-- On `[0, 1]`, the even Bernoulli polynomial attains its maximum modulus at the endpoints:
`|B_{2k}(x)| ≤ |B_{2k}|`. -/
theorem abs_bernoulliFun_even_le (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [bernoulliFun]
  · have h0 := hasSum_one_div_nat_pow_bernoulli hk
    have hx' := hasSum_cos_div_nat_pow_bernoulliFun hk hx
    have hpos : 0 < (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
      exact_mod_cast neg_one_pow_mul_bernoulli_two_mul_pos hk
    have hc : 0 < (2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ) := by positivity
    have hle : |(-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        bernoulliFun (2 * k) x| ≤
        (-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
          (bernoulli (2 * k) : ℝ) := by
      rw [← hx'.tsum_eq, ← h0.tsum_eq]
      refine (norm_tsum_le_tsum_norm hx'.summable.norm).trans
        (hx'.summable.norm.tsum_mono h0.summable fun n ↦ ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hc] at hle
    have habs : |(bernoulli (2 * k) : ℝ)| = (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
      simpa [abs_mul] using abs_of_pos hpos
    exact le_of_mul_le_mul_left (by rw [habs]; linarith) hc

/-- Periodic form of `neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg`: for every `k : ℕ`
and every real `u`, `0 ≤ (-1) ^ (k + 1) * (B_{2k} - B_{2k}({u}))`. -/
theorem neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg (k : ℕ) (u : ℝ) :
    0 ≤ (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract u)) :=
  neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg k
    ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩

/-- Periodic form of `abs_bernoulliFun_even_le`: for every `k : ℕ` and every real `u`,
`|B_{2k}({u})| ≤ |B_{2k}|`. -/
theorem abs_bernoulliFun_even_fract_le (k : ℕ) (u : ℝ) :
    |bernoulliFun (2 * k) (Int.fract u)| ≤ |(bernoulli (2 * k) : ℝ)| :=
  abs_bernoulliFun_even_le k ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩

end TauCeti
