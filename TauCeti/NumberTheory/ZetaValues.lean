/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues

/-!
# Bernoulli polynomials and Bernoulli functions

Mathlib's `bernoulliFun` is the real-variable Bernoulli polynomial. This file records how it
relates to the Bernoulli polynomial over `ℚ`, together with the sign and extremality properties of
the even Bernoulli numbers `B_{2k}` and even Bernoulli functions `B_{2k}(x)` on `[0, 1]`, deduced
from their cosine Fourier series (`hasSum_one_div_nat_pow_mul_cos` and `hasSum_zeta_nat`).

## Main results

* `TauCeti.bernoulliFun_ratCast`: `bernoulliFun` at a rational point is the Bernoulli polynomial
  over `ℚ` evaluated there, mapped into `ℝ`.
* `TauCeti.neg_one_pow_succ_mul_bernoulli_even_pos`: for `k ≥ 1`, `(-1) ^ (k + 1) * B_{2k} > 0`.
* `TauCeti.bernoulli_even_ne_zero`: for every `k : ℕ`, `B_{2k} ≠ 0`.
* `TauCeti.neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_nonneg`,
  `TauCeti.neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_pos`:
  `(-1) ^ (k + 1) * (B_{2k} - B_{2k}(x))` is nonnegative on `[0, 1]` for all `k` and strictly
  positive on `(0, 1)` for `k ≥ 1`.
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

/-- The positive Fourier normalization factor `(2 * π) ^ (2 * k) / 2 / (2 * k)!` appearing in the
cosine series of `B_{2k}(x)`. -/
private theorem bernoulli_fourier_factor_pos (k : ℕ) :
    0 < (2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ) := by
  positivity

/-- Euler's `ζ(2k)` identity written with the same Fourier factor as
`hasSum_one_div_nat_pow_mul_cos`. -/
private theorem hasSum_one_div_nat_pow_bernoulli {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        (bernoulli (2 * k) : ℝ)) := by
  convert hasSum_zeta_nat hk using 1
  have h2 : (2 : ℝ) ^ (2 * k - 1) = (2 : ℝ) ^ (2 * k) / 2 := by
    rw [eq_div_iff (two_ne_zero' ℝ), ← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [h2, mul_pow]
  ring

/-- Cosine Fourier series of `B_{2k}(x)` on `[0, 1]` with the factor grouped as in
`hasSum_one_div_nat_pow_bernoulli`. -/
private theorem hasSum_cos_div_nat_pow_bernoulliFun {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        bernoulliFun (2 * k) x) := by
  convert hasSum_one_div_nat_pow_mul_cos hk hx using 1
  rw [← bernoulliFun]
  ring

/-- The cosine series of `B_{2k} - B_{2k}(x)` for `k ≥ 1` and `x ∈ [0, 1]`. -/
private theorem hasSum_one_sub_cos_div_nat_pow {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ (1 - Real.cos (2 * π * n * x)) / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)) := by
  convert (hasSum_one_div_nat_pow_bernoulli hk).sub (hasSum_cos_div_nat_pow_bernoulliFun hk hx)
    using 1
  · ext n
    ring
  · ring

/-- The even Bernoulli numbers alternate strictly in sign: for `k ≥ 1`,
`(-1) ^ (k + 1) * B_{2k} > 0`. -/
theorem neg_one_pow_succ_mul_bernoulli_even_pos {k : ℕ} (hk : k ≠ 0) :
    0 < (-1 : ℚ) ^ (k + 1) * bernoulli (2 * k) := by
  suffices h : 0 < (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) by exact_mod_cast h
  have h0 := hasSum_one_div_nat_pow_bernoulli hk
  have hsum_pos : 0 < (-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
      (bernoulli (2 * k) : ℝ) := by
    rw [← h0.tsum_eq]
    refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / ((1 : ℕ) : ℝ) ^ (2 * k)) ?_
    exact h0.summable.le_tsum (1 : ℕ) (fun n _ ↦ by positivity)
  exact pos_of_mul_pos_right (by linarith :
      0 < ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        ((-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ)))
    (bernoulli_fourier_factor_pos k).le

/-- Every even Bernoulli number `B_{2k}` is nonzero. -/
theorem bernoulli_even_ne_zero (k : ℕ) : bernoulli (2 * k) ≠ 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · intro h
    have hpos := neg_one_pow_succ_mul_bernoulli_even_pos hk
    rw [h, mul_zero] at hpos
    exact lt_irrefl 0 hpos

/-- For `x ∈ [0, 1]`, the difference `B_{2k} - B_{2k}(x)` satisfies
`0 ≤ (-1) ^ (k + 1) * (B_{2k} - B_{2k}(x))`. -/
theorem neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_nonneg (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [bernoulliFun]
  · have hsum := hasSum_one_sub_cos_div_nat_pow hk hx
    have hge : 0 ≤ (-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := by
      rw [← hsum.tsum_eq]
      exact tsum_nonneg fun n ↦ div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by positivity)
    exact nonneg_of_mul_nonneg_right (by linarith :
        0 ≤ ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
          ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)))
      (bernoulli_fourier_factor_pos k)

/-- For `k ≥ 1` and `x ∈ (0, 1)`, the difference `B_{2k} - B_{2k}(x)` strictly has the sign of
`B_{2k}`: `0 < (-1) ^ (k + 1) * (B_{2k} - B_{2k}(x))`. -/
theorem neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_pos {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := by
  have hsum := hasSum_one_sub_cos_div_nat_pow hk (Set.Ioo_subset_Icc_self hx)
  have hcos : Real.cos (2 * π * x) < 1 := by
    have hne : Real.cos (2 * π * x) ≠ 1 := by
      intro h
      rw [Real.cos_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      have hm_eq : (m : ℝ) = x :=
        mul_right_cancel₀ (by positivity : (2 : ℝ) * π ≠ 0) (by linarith [hm])
      have hm0 : (0 : ℤ) < m := by exact_mod_cast (by linarith [hx.1] : (0 : ℝ) < m)
      have hm1 : m < (1 : ℤ) := by exact_mod_cast (by linarith [hx.2] : (m : ℝ) < 1)
      omega
    exact lt_of_le_of_ne (Real.cos_le_one (2 * π * x)) hne
  have hterm1 : 0 < (1 - Real.cos (2 * π * ((1 : ℕ) : ℝ) * x)) / ((1 : ℕ) : ℝ) ^ (2 * k) := by
    simpa only [Nat.cast_one, mul_one, one_pow, div_one, sub_pos] using hcos
  have hgt : 0 < (-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
      ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := by
    rw [← hsum.tsum_eq]
    exact lt_of_lt_of_le hterm1 (hsum.summable.le_tsum (1 : ℕ) fun n _ ↦
      div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by positivity))
  exact pos_of_mul_pos_right (by linarith :
      0 < ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)))
    (bernoulli_fourier_factor_pos k).le

/-- On `[0, 1]`, the even Bernoulli polynomial attains its maximum modulus at the endpoints:
`|B_{2k}(x)| ≤ |B_{2k}|`. -/
theorem abs_bernoulliFun_even_le (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [bernoulliFun]
  · have h0 := hasSum_one_div_nat_pow_bernoulli hk
    have hx' := hasSum_cos_div_nat_pow_bernoulliFun hk hx
    have hpos : 0 < (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
      exact_mod_cast neg_one_pow_succ_mul_bernoulli_even_pos hk
    have habs : |(bernoulli (2 * k) : ℝ)| = (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
      rw [← abs_of_pos hpos, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hle : |(-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
        bernoulliFun (2 * k) x| ≤
        (-1 : ℝ) ^ (k + 1) * ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) *
          (bernoulli (2 * k) : ℝ) := by
      rw [← hx'.tsum_eq, ← h0.tsum_eq]
      refine (norm_tsum_le_tsum_norm hx'.summable.norm).trans ?_
      refine hx'.summable.norm.tsum_mono h0.summable fun n ↦ ?_
      dsimp only
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k))]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (bernoulli_fourier_factor_pos k)] at hle
    have hle' : ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) * |bernoulliFun (2 * k) x| ≤
        ((2 * π) ^ (2 * k) / 2 / ((2 * k)! : ℝ)) * |(bernoulli (2 * k) : ℝ)| := by
      rw [habs]
      linarith
    exact le_of_mul_le_mul_left hle' (bernoulli_fourier_factor_pos k)

/-- Periodic form of `neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_nonneg`: for every `k : ℕ`
and every real `u`, `0 ≤ (-1) ^ (k + 1) * (B_{2k} - B_{2k}({u}))`. -/
theorem neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg (k : ℕ) (u : ℝ) :
    0 ≤ (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract u)) :=
  neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_nonneg k
    ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩

/-- Periodic form of `abs_bernoulliFun_even_le`: for every `k : ℕ` and every real `u`,
`|B_{2k}({u})| ≤ |B_{2k}|`. -/
theorem abs_bernoulliFun_even_fract_le (k : ℕ) (u : ℝ) :
    |bernoulliFun (2 * k) (Int.fract u)| ≤ |(bernoulli (2 * k) : ℝ)| :=
  abs_bernoulliFun_even_le k ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩

end TauCeti
