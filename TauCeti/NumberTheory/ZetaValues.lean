/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.NumberTheory.Bernoulli.Values

/-!
# Bernoulli polynomials and Bernoulli functions

Mathlib's `bernoulliFun` is the real-variable Bernoulli polynomial, and
`Mathlib.NumberTheory.ZetaValues` computes the Fourier series of `bernoulliFun` on `[0, 1]`
together with Euler's formula for `ζ(2 * k)`. This file records how `bernoulliFun` relates to the
Bernoulli polynomial over `ℚ`, uniform bounds on `[0, 1]`, and how the even ones compare with
their value at `0` on `[0, 1]`.

## Main results

* `TauCeti.bernoulliFun_ratCast`: `bernoulliFun` at a rational point is the Bernoulli polynomial
  over `ℚ` evaluated there, mapped into `ℝ`.
* `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg` and
  `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_pos`: on `[0, 1]`,
  `B_{2k} - B_{2k}(x)` has the sign `(-1)^(k+1)` of `B_{2k}` (or vanishes), and strictly so on
  `(0, 1)` when `k ≠ 0`. This makes the remainder of the Euler–Maclaurin formula of even order a
  one-signed integral, so that for monotone derivatives the remainder is enclosed by the first
  neglected term.
* `TauCeti.abs_bernoulliFun_le_mul_tsum`: for `2 ≤ k` and `x ∈ [0, 1]`,
  `|B_k(x)| ≤ 2 · k! / (2π)^k · ∑_{n : ℕ} 1 / n^k`, the last sum being `ζ(k)`.
* `TauCeti.abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div`: for every `k` and
  `x ∈ [0, 1]`, `|B_k(x)| ≤ π² / 3 · k! / (2π)^k`; equality holds for `k = 2`, `x = 0`.
* `TauCeti.abs_bernoulliFun_le_four_mul_factorial_div`: the weaker
  `|B_k(x)| ≤ 4 · k! / (2π)^k`.
* `TauCeti.hasSum_one_div_nat_pow_mul_one_sub_cos`: Fourier series of
  `bernoulli (2 * k) - bernoulliFun (2 * k) x` on `[0, 1]`.
* `TauCeti.abs_bernoulliFun_le_abs_bernoulli`,
  `TauCeti.abs_bernoulliFun_fract_le_abs_bernoulli`, and
  `TauCeti.abs_bernoulli_sub_bernoulliFun_fract_le`: Lehmer's bound `|B_{2k}(x)| ≤ |B_{2k}|` on
  `[0, 1]` and the periodic bounds `|B_{2k}({x})| ≤ |B_{2k}|` and
  `|B_{2k} - B_{2k}({x})| ≤ 2 |B_{2k}|` on `ℝ`.

The sign and strict positivity follow from the Fourier cosine series
`hasSum_one_div_nat_pow_mul_cos`: up to the positive factor `(2π)^(2k) / (2 (2k)!)`,
`(-1)^(k+1) (B_{2k} - B_{2k}(x))` is `∑_{n ≥ 1} (1 - cos (2π n x)) / n^(2k) ≥ 0`.

The uniform bounds follow from the Fourier series `hasSum_one_div_nat_pow_mul_fourier`:
`-(2πi)^k / k! · B_k(x) = ∑_{n ≥ 1} n^(-k) (e(nx) + (-1)^k e(-nx))` for `k ≥ 2`, whose terms
have norm at most `2 n^(-k)`, together with `ζ(k) ≤ ζ(2) = π² / 6` (and Euler's formula for
`ζ(2k)` in the even case); the cases `k = 0, 1` are checked directly.

## References

* The bound `|B_k(x)| ≤ 4 · k! / (2π)^k` on `[0, 1]` is the estimate used to bound generalized
  Bernoulli numbers in the proof of `UpperTheory.V.Odd.PrimeBound` in
  https://github.com/leanprover-community/riemann-hypothesis, the source of the statement.
* NIST *Digital Library of Mathematical Functions*, §§24.8(i), 24.9(i), formulas 24.8.1–24.8.3
  and 24.9.2.
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

/-- For `2 ≤ k` and `x ∈ [0, 1]`, `|B_k(x)| ≤ 2 · k! / (2π)^k · ∑_{n : ℕ} 1 / n^k`, i.e.
`|B_k(x)| ≤ 2 · k! · ζ(k) / (2π)^k`. Everything is in `ℝ`, and the `n = 0` term of the sum is
`1 / 0 = 0`. -/
theorem abs_bernoulliFun_le_mul_tsum {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 2 * k ! / (2 * π) ^ k * ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
  have hS : HasSum (fun n : ℕ => 2 * (1 / (n : ℝ) ^ k)) (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ k) :=
    (Real.summable_one_div_nat_pow.mpr hk).hasSum.mul_left 2
  have h := (hasSum_one_div_nat_pow_mul_fourier hk hx).norm_le_of_bounded hS fun n => by
    rw [norm_mul, mul_comm]
    have hn : ‖(1 : ℂ) / (n : ℂ) ^ k‖ = 1 / (n : ℝ) ^ k := by simp
    rw [hn]
    gcongr
    refine (norm_add_le _ _).trans ?_
    norm_num [Circle.norm_coe]
  have hn : ‖-(2 * π * Complex.I) ^ k / k ! * (bernoulliFun k x : ℂ)‖ =
      |bernoulliFun k x| * ((2 * π) ^ k / k !) := by
    simp [abs_of_pos Real.pi_pos, mul_comm]
  rw [hn, ← le_div_iff₀ (by positivity)] at h
  exact h.trans_eq (by field_simp)

/-- For every `k : ℕ` and `x ∈ [0, 1]`, `|B_k(x)| ≤ π² / 3 · k! / (2π)^k`, with `k!` cast to
`ℝ`. For `2 ≤ k` this follows from `TauCeti.abs_bernoulliFun_le_mul_tsum` and
`∑_{n : ℕ} 1 / n^k ≤ π² / 6`. The constant is attained at `k = 2`, `x = 0`, where both sides
are `1 / 6`. -/
theorem abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliFun k x| ≤ π ^ 2 / 3 * k ! / (2 * π) ^ k := by
  obtain _ | _ | k := k
  · have : (3 : ℝ) ^ 2 ≤ π ^ 2 := by gcongr; exact Real.pi_gt_three.le
    simp only [bernoulliFun_zero, abs_one, Nat.factorial_zero, Nat.cast_one, pow_zero]
    linarith
  · have h : 1 / 2 ≤ π ^ 2 / 3 * (1 : ℕ)! / (2 * π) ^ 1 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    rw [bernoulliFun_one, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  · have hle : ∑' n : ℕ, 1 / (n : ℝ) ^ (k + 2) ≤ π ^ 2 / 6 := by
      refine hasSum_le (fun n => ?_) (Real.summable_one_div_nat_pow.mpr (by omega)).hasSum
        hasSum_zeta_two
      rcases n.eq_zero_or_pos with rfl | hn
      · simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        gcongr
        omega
    refine (abs_bernoulliFun_le_mul_tsum (by omega) hx).trans ?_
    calc 2 * (k + 2)! / (2 * π) ^ (k + 2) * ∑' n : ℕ, 1 / (n : ℝ) ^ (k + 2)
        ≤ 2 * (k + 2)! / (2 * π) ^ (k + 2) * (π ^ 2 / 6) := by gcongr
      _ = π ^ 2 / 3 * (k + 2)! / (2 * π) ^ (k + 2) := by ring

/-- For every `k : ℕ` and `x ∈ [0, 1]`, `|B_k(x)| ≤ 4 · k! / (2π)^k`, with `k!` cast to `ℝ`:
the bound `TauCeti.abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div` with `π² / 3 < 4`. -/
theorem abs_bernoulliFun_le_four_mul_factorial_div (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliFun k x| ≤ 4 * k ! / (2 * π) ^ k := by
  refine (abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div k hx).trans ?_
  have : π ^ 2 < 3.15 ^ 2 := by gcongr; exact Real.pi_lt_d2
  gcongr
  linarith

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
      rw [mul_assoc 2 π x, Real.cos_two_mul', Real.cos_sq']
      ring
    rwa [hcos] at hle
  have hpos : 0 < ((2 * π) ^ (2 * k) / 2 / (2 * k)!) *
      ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)) :=
    calc (0 : ℝ) < 2 * Real.sin (π * x) ^ 2 := by positivity
      _ ≤ (-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
          ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x) := h1
      _ = ((2 * π) ^ (2 * k) / 2 / (2 * k)!) *
          ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℝ) - bernoulliFun (2 * k) x)) := by ring
  exact pos_of_mul_pos_right hpos (by positivity)

/-- **Lehmer's bound** for even Bernoulli polynomials on `[0, 1]` (DLMF 24.9.2):
`|B_{2k}(x)| ≤ |B_{2k}|` for every `k : ℕ` and `x ∈ [0, 1]`. -/
theorem abs_bernoulliFun_le_abs_bernoulli (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun (2 * k) x| ≤ |(bernoulli (2 * k) : ℝ)| := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have habsB : |(bernoulli (2 * k) : ℝ)| = (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
    exact_mod_cast abs_bernoulli_two_mul hk
  refine (abs_bernoulliFun_le_mul_tsum (by omega) hx).trans_eq ?_
  rw [(hasSum_zeta_nat hk).tsum_eq, habsB, two_pi_pow_two_mul hk]
  have hfac : ((2 * k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpi : π ^ (2 * k) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have htwo : (2 : ℝ) ^ (2 * k - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp

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
