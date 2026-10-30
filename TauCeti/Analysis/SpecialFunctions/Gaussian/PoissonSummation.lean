/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum

/-!
# Poisson summation for Gaussian lattice sums

This file rewrites the shifted Gaussian lattice sum as its Fourier series.  The identity is the
Poisson summation formula for a translated Gaussian and is the analytic bridge from
`Real.gaussianLatticeSum` to periodized Gaussian densities.

For positive width `s`,

`Z(c, s) = sqrt (2 * pi) * s * sum n, exp (-2 * pi^2 * s^2 * n^2) * cos (2 * pi * n * c)`.

The Fourier series converges absolutely.  Splitting the integer sum into its zero term and paired
positive and negative terms gives the corresponding one-sided cosine series used for wrapped
normal densities.  The proof specializes Mathlib's `Complex.tsum_exp_neg_quadratic`.

## References

* K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley, 2000, section 3.5.
-/

public section

noncomputable section

open Complex

namespace Real

private theorem cpow_two_mul_pi_mul_sq (s : ℝ) (hs : 0 < s) :
    (((2 * π * s ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = ((sqrt (2 * π) * s : ℝ) : ℂ) := by
  have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [hexp]
  rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * π * s ^ 2)]
  congr 1
  rw [← sqrt_eq_rpow]
  calc
    sqrt (2 * π * s ^ 2) = sqrt (2 * π) * sqrt (s ^ 2) := by
      rw [sqrt_mul (by positivity : 0 ≤ 2 * π)]
    _ = sqrt (2 * π) * s := by rw [sqrt_sq hs.le]

private theorem summable_gaussianLatticeFourierCoeff {s : ℝ} (hs : s ≠ 0) :
    Summable fun n : ℤ ↦ rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) := by
  have h := summable_abs_pow_mul_exp_neg_sub_sq_div 0 0
    (inv_pos.mpr (mul_pos (mul_pos two_pos (sq_pos_of_pos pi_pos)) (sq_pos_of_ne_zero hs)))
  refine h.congr fun n ↦ ?_
  simp only [pow_zero, one_mul, sub_zero]
  congr 1
  field_simp

private theorem summable_complex_gaussianLatticeFourier
    (c : ℝ) {s : ℝ} (hs : 0 < s) :
    Summable fun n : ℤ ↦
      ((rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) *
        cexp (2 * π * I * (n : ℂ) * c) := by
  refine (summable_gaussianLatticeFourierCoeff hs.ne').of_norm_bounded fun n ↦ ?_
  have hre : (2 * π * I * (n : ℂ) * c).re = 0 := by
    simp
  rw [norm_mul, norm_real, norm_exp]
  rw [hre, exp_zero, mul_one, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

private theorem gaussianLatticeSum_eq_complex_fourier (c : ℝ) {s : ℝ} (hs : 0 < s) :
    (gaussianLatticeSum c s : ℂ) =
      ((sqrt (2 * π) * s : ℝ) : ℂ) *
        ∑' n : ℤ,
          ((rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) *
            cexp (2 * π * I * (n : ℂ) * c) := by
  have ha : 0 < (((2 * π * s ^ 2 : ℝ) : ℂ)).re := by
    norm_num [mul_re, pow_two]
    positivity
  have h := Complex.tsum_exp_neg_quadratic ha (I * c)
  have hleft :
      (∑' n : ℤ, cexp (-π * ((2 * π * s ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ 2 +
          2 * π * (I * c) * n)) =
        ∑' n : ℤ,
          ((rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) *
            cexp (2 * π * I * (n : ℂ) * c) := by
    apply tsum_congr
    intro n
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hright :
      (∑' n : ℤ, cexp (-π / ((2 * π * s ^ 2 : ℝ) : ℂ) *
          (n + I * (I * c)) ^ 2)) = (gaussianLatticeSum c s : ℂ) := by
    rw [gaussianLatticeSum_def, ofReal_tsum]
    apply tsum_congr
    intro n
    rw [ofReal_exp]
    congr 1
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
  rw [hleft, hright, cpow_two_mul_pi_mul_sq s hs] at h
  have hscale : (((sqrt (2 * π) * s : ℝ) : ℂ)) ≠ 0 :=
    ofReal_ne_zero.mpr (mul_ne_zero (sqrt_ne_zero'.mpr (by positivity)) hs.ne')
  calc
    (gaussianLatticeSum c s : ℂ) = ((sqrt (2 * π) * s : ℝ) : ℂ) *
        (1 / ((sqrt (2 * π) * s : ℝ) : ℂ) * (gaussianLatticeSum c s : ℂ)) := by
      field_simp
    _ = ((sqrt (2 * π) * s : ℝ) : ℂ) *
        ∑' n : ℤ,
          ((rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) *
            cexp (2 * π * I * (n : ℂ) * c) := by rw [← h]

/-- The real cosine series in the Gaussian Poisson summation formula is absolutely summable for
every nonzero width. -/
theorem summable_gaussianLatticeFourier (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    Summable fun n : ℤ ↦
      rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c) := by
  refine (summable_gaussianLatticeFourierCoeff hs).of_norm_bounded fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (exp_nonneg _) (abs_cos_le_one _)

/-- For every nonzero width, the Fourier series in the Gaussian Poisson formula converges uniformly
in the centre. -/
theorem hasSumUniformly_gaussianLatticeFourier {s : ℝ} (hs : s ≠ 0) :
    HasSumUniformly
      (fun n : ℤ ↦ fun c : ℝ ↦
        rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c))
      (fun c ↦ ∑' n : ℤ,
        rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c)) := by
  rw [← hasSumUniformlyOn_univ_iff]
  refine HasSumUniformlyOn.of_norm_le_summable
    (summable_gaussianLatticeFourierCoeff hs) ?_
  intro n c _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_right (exp_nonneg _) (abs_cos_le_one _)

/-- **Poisson summation for the Gaussian lattice sum.** For positive width, `Z(c, s)` is the
absolutely convergent Fourier series with coefficients `sqrt (2π) s exp (-2π²s²n²)`. -/
theorem gaussianLatticeSum_eq_fourier (c : ℝ) {s : ℝ} (hs : 0 < s) :
    gaussianLatticeSum c s = sqrt (2 * π) * s *
      ∑' n : ℤ,
        rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c) := by
  have hterm (n : ℤ) :
      ((((rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) : ℝ) : ℂ) *
          cexp (2 * π * I * (n : ℂ) * c))).re =
        rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c) := by
    have hexp :
        cexp (2 * π * I * (n : ℂ) * c) =
          cexp (((2 * π * (n : ℝ) * c : ℝ) : ℂ) * I) := by
      congr 1
      push_cast
      ring
    rw [hexp, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  have h := congrArg Complex.re (gaussianLatticeSum_eq_complex_fourier c hs)
  rw [ofReal_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    Complex.re_tsum (summable_complex_gaussianLatticeFourier c hs)] at h
  simp_rw [hterm] at h
  exact h

/-- The Gaussian Poisson formula with the zero mode separated and the positive and negative
frequencies paired.  This is the usual one-sided cosine-series form. -/
theorem gaussianLatticeSum_eq_cosineSeries (c : ℝ) {s : ℝ} (hs : 0 < s) :
    gaussianLatticeSum c s = sqrt (2 * π) * s *
      (1 + 2 * ∑' n : ℕ,
        rexp (-2 * π ^ 2 * s ^ 2 * (n + 1 : ℝ) ^ 2) *
          cos (2 * π * (n + 1 : ℝ) * c)) := by
  let f : ℤ → ℝ := fun n ↦
    rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c)
  have hf : f.Even := by
    intro n
    simp only [f, Int.cast_neg, neg_sq]
    rw [show 2 * π * -(n : ℝ) * c = -(2 * π * (n : ℝ) * c) by ring, cos_neg]
  have hp : (∑' n : ℕ+, f n) = ∑' n : ℕ, f (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f n)
  rw [gaussianLatticeSum_eq_fourier c hs,
    tsum_int_eq_zero_add_two_mul_tsum_pnat hf (summable_gaussianLatticeFourier c hs.ne'), hp]
  simp [f, nsmul_eq_mul]

end Real
