/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
import TauCeti.NumberTheory.Bernoulli.Values

/-!
# Bernoulli polynomials and periodic bounds

Mathlib's `bernoulliFun` is the real-variable Bernoulli polynomial, and
`Mathlib.NumberTheory.ZetaValues` computes the Fourier cosine series of `bernoulliFun (2 * k)` on
`[0, 1]` together with Euler's formula for `ζ(2 * k)`. This file records how `bernoulliFun` relates
to the Bernoulli polynomial over `ℚ`, and how the even ones compare with their value at `0` on
`[0, 1]`. Subtracting the cosine series from its value at `x = 0` expresses
`(-1)^(k + 1) * (B_{2k} - B_{2k}(x))` as a series with nonnegative terms, strictly positive on
`(0, 1)` for `k ≠ 0`. Together with the triangle inequality on the cosine series, this gives
Lehmer's bound `|B_{2k}(x)| ≤ |B_{2k}|` on `[0, 1]` (DLMF 24.9.2) and its periodic versions
evaluated at `Int.fract x`.

## Main results

* `TauCeti.bernoulliFun_ratCast`: `bernoulliFun` at a rational point is the Bernoulli polynomial
  over `ℚ` evaluated there, mapped into `ℝ`.
* `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg` and
  `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_pos`: on `[0, 1]`,
  `B_{2k} - B_{2k}(x)` has the sign `(-1)^(k+1)` of `B_{2k}` (or vanishes), and strictly so on
  `(0, 1)` when `k ≠ 0`. This makes the remainder of the Euler–Maclaurin formula of even order a
  one-signed integral, so that for monotone derivatives the remainder is enclosed by the first
  neglected term.
* `TauCeti.hasSum_one_div_nat_pow_mul_one_sub_cos`: Fourier series of
  `bernoulli (2 * k) - bernoulliFun (2 * k) x` on `[0, 1]`.
* `TauCeti.abs_bernoulliFun_le_abs_bernoulli`,
  `TauCeti.abs_bernoulliFun_fract_le_abs_bernoulli`, and
  `TauCeti.abs_bernoulli_sub_bernoulliFun_fract_le`: `|B_{2k}(x)| ≤ |B_{2k}|` on `[0, 1]` and
  `|B_{2k} - B_{2k}({x})| ≤ 2 |B_{2k}|` on `ℝ`.

## References

* NIST *Digital Library of Mathematical Functions*, §§24.8(i), 24.9(i), formulas 24.8.3 and 24.9.2.
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

/-- Periodic form of `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg`: for every `k : ℕ`
and `x : ℝ`, `(-1)^(k + 1) * (B_{2k} - B_{2k}({x})) ≥ 0`. -/
theorem neg_one_pow_mul_bernoulli_sub_bernoulliFun_fract_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ (-1 : ℝ) ^ (k + 1) *
      ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract x)) :=
  neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg k
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-- Rewrite `(2 * π) ^ (2 * k)` as `2 * 2 ^ (2 * k - 1) * π ^ (2 * k)` when `k ≠ 0`. -/
private theorem two_pi_pow_two_mul {k : ℕ} (hk : k ≠ 0) :
    (2 * π) ^ (2 * k) = 2 * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) := by
  have h2 : (2 : ℝ) ^ (2 * k) = 2 * (2 : ℝ) ^ (2 * k - 1) := by
    conv_lhs => rw [show 2 * k = (2 * k - 1) + 1 by omega, pow_succ']
  rw [mul_pow, h2]

/-- For `k ≠ 0`, `|bernoulli (2 * k)| = (-1)^(k + 1) * bernoulli (2 * k)`. -/
theorem abs_bernoulli_two_mul {k : ℕ} (hk : k ≠ 0) :
    |bernoulli (2 * k)| = (-1 : ℚ) ^ (k + 1) * bernoulli (2 * k) := by
  have h := abs_of_pos (neg_one_pow_mul_bernoulli_two_mul_pos hk)
  rwa [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h

/-- Fourier series for `bernoulli (2 * k) - bernoulliFun (2 * k) x` on `[0, 1]` (`k ≠ 0`),
obtained by subtracting `hasSum_one_div_nat_pow_mul_cos` from `hasSum_zeta_nat`. -/
theorem hasSum_one_div_nat_pow_mul_one_sub_cos {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k) * (1 - Real.cos (2 * π * n * x)))
      ((-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
        ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)) := by
  have h0 := hasSum_zeta_nat hk
  have hx' := hasSum_one_div_nat_pow_mul_cos hk hx
  rw [← bernoulliFun] at hx'
  convert h0.sub hx' using 1
  · ext n
    ring
  · rw [two_pi_pow_two_mul hk]
    ring

/-- On `(0, 1)`, `(-1)^(k + 1) * (B_{2k} - B_{2k}(x)) > 0` strictly for every `k ≠ 0`. -/
theorem neg_one_pow_mul_bernoulli_sub_bernoulliFun_pos {k : ℕ} (hk : k ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := by
  have hsum := hasSum_one_div_nat_pow_mul_one_sub_cos hk (Set.Ioo_subset_Icc_self hx)
  have hsin : 0 < Real.sin (π * x) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx.1)
      (by nlinarith [Real.pi_pos, hx.2])
  have h1 : 2 * Real.sin (π * x) ^ 2 ≤
      (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
        ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := by
    have hle := sum_le_hasSum ({1} : Finset ℕ)
      (fun n _ => mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))) hsum
    simp only [Finset.sum_singleton, Nat.cast_one, one_pow, div_one, one_mul, mul_one] at hle
    have hcos : 1 - Real.cos (2 * π * x) = 2 * Real.sin (π * x) ^ 2 := by
      rw [show 2 * π * x = 2 * (π * x) by ring, Real.cos_two_mul', Real.cos_sq']
      ring
    rwa [hcos] at hle
  have hpos : 0 < (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
      ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) :=
    (by positivity : 0 < 2 * Real.sin (π * x) ^ 2).trans_le h1
  have hfac : (0 : ℝ) < (2 * π) ^ (2 * k) / 2 / (2 * k)! := by positivity
  exact pos_of_mul_pos_left
    (by simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hpos) hfac.le

/-- **Lehmer's bound** for even Bernoulli polynomials on `[0, 1]` (DLMF 24.9.2):
`|B_{2k}(x)| ≤ |B_{2k}|` for every `k : ℕ` and `x ∈ [0, 1]`. -/
theorem abs_bernoulliFun_le_abs_bernoulli (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hcos := hasSum_one_div_nat_pow_mul_cos hk hx
  rw [← bernoulliFun] at hcos
  have hzeta := hasSum_zeta_nat hk
  have hnorm : |(-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
        bernoulliFun (2 * k) x| ≤
      (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
        bernoulli (2 * k) / (2 * k)! := by
    rw [← hcos.tsum_eq, ← hzeta.tsum_eq, ← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hcos.summable.norm).trans ?_
    exact Summable.tsum_le_tsum (fun n => by
      have hpow : (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * k) := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
      exact mul_le_of_le_one_right hpow (Real.abs_cos_le_one _))
      hcos.summable.norm hzeta.summable
  have hfac : (0 : ℝ) < (2 * π) ^ (2 * k) / 2 / (2 * k)! := by positivity
  have habsB : |(bernoulli (2 * k) : ℝ)| = (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
    exact_mod_cast abs_bernoulli_two_mul hk
  rw [abs_mul, abs_div, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π) ^ (2 * k)), abs_of_pos zero_lt_two,
    abs_of_pos (by positivity : (0 : ℝ) < ((2 * k)! : ℝ))] at hnorm
  have hnorm' : ((2 * π) ^ (2 * k) / 2 / (2 * k)!) * |bernoulliFun (2 * k) x| ≤
      ((2 * π) ^ (2 * k) / 2 / (2 * k)!) * |(bernoulli (2 * k) : ℝ)| := by
    rw [two_pi_pow_two_mul hk] at hnorm ⊢
    rw [habsB]
    linarith [show (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
        bernoulli (2 * k) / (2 * k)! =
      (2 * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) / 2 / (2 * k)!) *
        ((-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ)) by ring]
  exact le_of_mul_le_mul_left hnorm' hfac

/-- Periodic form of `abs_bernoulliFun_le_abs_bernoulli`: `|B_{2k}({x})| ≤ |B_{2k}|` on `ℝ`. -/
theorem abs_bernoulliFun_fract_le_abs_bernoulli (k : ℕ) (x : ℝ) :
    |bernoulliFun (2 * k) (Int.fract x)| ≤ |(bernoulli (2 * k) : ℝ)| :=
  abs_bernoulliFun_le_abs_bernoulli k ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

/-- On `ℝ`, the periodic Euler–Maclaurin kernel `B_{2k} - B_{2k}({x})` satisfies
`|B_{2k} - B_{2k}({x})| ≤ 2 * |B_{2k}|`. -/
theorem abs_bernoulli_sub_bernoulliFun_fract_le (k : ℕ) (x : ℝ) :
    |(bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract x)| ≤
      2 * |(bernoulli (2 * k) : ℝ)| := by
  calc
    |(bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) (Int.fract x)| ≤
        |(bernoulli (2 * k) : ℝ)| + |bernoulliFun (2 * k) (Int.fract x)| := abs_sub _ _
    _ ≤ |(bernoulli (2 * k) : ℝ)| + |(bernoulli (2 * k) : ℝ)| :=
      add_le_add_right (abs_bernoulliFun_fract_le_abs_bernoulli k x) _
    _ = 2 * |(bernoulli (2 * k) : ℝ)| := by ring

end TauCeti
