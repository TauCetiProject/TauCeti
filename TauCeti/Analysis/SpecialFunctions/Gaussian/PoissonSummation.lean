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

For every width `s`,

`Z(c, s) = sqrt (2 * pi) * |s| * sum n, exp (-2 * pi^2 * s^2 * n^2) * cos (2 * pi * n * c)`.

The Fourier series converges absolutely, and uniformly in the centre `c`.  Splitting the integer
sum into its zero term and paired positive and negative terms gives the corresponding one-sided
cosine series used for wrapped normal densities.  The proof specializes Mathlib's
`Complex.tsum_exp_neg_quadratic`.

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
  simp [norm_exp, -ofReal_exp]

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
    rw [ofReal_exp, ← mul_assoc I I, I_mul_I]
    congr 1
    push_cast
    field_simp
    ring
  rw [hleft, hright, cpow_two_mul_pi_mul_sq s hs] at h
  have hscale : (((sqrt (2 * π) * s : ℝ) : ℂ)) ≠ 0 :=
    ofReal_ne_zero.mpr (mul_ne_zero (sqrt_ne_zero'.mpr (by positivity)) hs.ne')
  rw [h]
  field_simp

/-- The real cosine series in the Gaussian Poisson summation formula is absolutely summable for
every nonzero width. -/
theorem summable_gaussianLatticeFourier (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    Summable fun n : ℤ ↦
      rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c) :=
  (summable_gaussianLatticeFourierCoeff hs).of_norm_bounded fun _ ↦
    (norm_mul_le_of_le (norm_of_nonneg (exp_nonneg _)).le (abs_cos_le_one _)).trans_eq (mul_one _)

private theorem gaussianLatticeSum_eq_fourier_of_pos (c : ℝ) {s : ℝ} (hs : 0 < s) :
    gaussianLatticeSum c s = sqrt (2 * π) * s *
      ∑' n : ℤ,
        rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c) := by
  have h := congrArg Complex.re (gaussianLatticeSum_eq_complex_fourier c hs)
  rw [re_ofReal_mul, Complex.re_tsum (summable_complex_gaussianLatticeFourier c hs)] at h
  simpa [re_ofReal_mul, exp_re, -ofReal_exp] using h

/-- **Poisson summation for the Gaussian lattice sum.** `Z(c, s)` is the absolutely convergent
Fourier series with coefficients `sqrt (2π) |s| exp (-2π²s²n²)`. -/
theorem gaussianLatticeSum_eq_fourier (c s : ℝ) :
    gaussianLatticeSum c s = sqrt (2 * π) * |s| *
      ∑' n : ℤ,
        rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c) := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · rw [← gaussianLatticeSum_neg_right, gaussianLatticeSum_eq_fourier_of_pos c (neg_pos.mpr hs),
      abs_of_neg hs, neg_sq]
  · simp [gaussianLatticeSum_zero_right]
  · rw [gaussianLatticeSum_eq_fourier_of_pos c hs, abs_of_pos hs]

/-- The Gaussian Poisson formula as a `HasSum` statement: the Fourier series with coefficients
`sqrt (2π) |s| exp (-2π²s²n²)` sums to `Z(c, s)`. -/
theorem hasSum_gaussianLatticeFourier (c s : ℝ) :
    HasSum (fun n : ℤ ↦
        sqrt (2 * π) * |s| * rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) *
          cos (2 * π * (n : ℝ) * c))
      (gaussianLatticeSum c s) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [gaussianLatticeSum_zero_right]
  rw [gaussianLatticeSum_eq_fourier c s]
  convert (summable_gaussianLatticeFourier c hs).hasSum.mul_left (sqrt (2 * π) * |s|) using 1
  funext n
  ring

/-- The Fourier series of the Gaussian lattice sum converges to `Z(c, s)` uniformly in the
centre `c`. -/
theorem hasSumUniformly_gaussianLatticeFourier (s : ℝ) :
    HasSumUniformly
      (fun n : ℤ ↦ fun c : ℝ ↦
        sqrt (2 * π) * |s| * rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) *
          cos (2 * π * (n : ℝ) * c))
      (fun c ↦ gaussianLatticeSum c s) := by
  have hu : Summable fun n : ℤ ↦
      sqrt (2 * π) * |s| * rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) := by
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    exact (summable_gaussianLatticeFourierCoeff hs).mul_left _
  simp_rw [← (hasSum_gaussianLatticeFourier _ s).tsum_eq, ← hasSumUniformlyOn_univ_iff]
  exact .of_norm_le_summable hu fun _ _ _ ↦
    (norm_mul_le_of_le (norm_of_nonneg (by positivity)).le (abs_cos_le_one _)).trans_eq (mul_one _)

/-- The Gaussian Poisson formula with the zero mode separated and the positive and negative
frequencies paired.  This is the usual one-sided cosine-series form. -/
theorem gaussianLatticeSum_eq_cosineSeries (c s : ℝ) :
    gaussianLatticeSum c s = sqrt (2 * π) * |s| *
      (1 + 2 * ∑' n : ℕ,
        rexp (-2 * π ^ 2 * s ^ 2 * (n + 1 : ℝ) ^ 2) *
          cos (2 * π * (n + 1 : ℝ) * c)) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [gaussianLatticeSum_zero_right]
  let f : ℤ → ℝ := fun n ↦
    rexp (-2 * π ^ 2 * s ^ 2 * (n : ℝ) ^ 2) * cos (2 * π * (n : ℝ) * c)
  have hf : f.Even := by
    intro n
    simp only [f, Int.cast_neg, neg_sq]
    rw [show 2 * π * -(n : ℝ) * c = -(2 * π * (n : ℝ) * c) by ring, cos_neg]
  have hp : (∑' n : ℕ+, f n) = ∑' n : ℕ, f (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f n)
  rw [gaussianLatticeSum_eq_fourier c s,
    tsum_int_eq_zero_add_two_mul_tsum_pnat hf (summable_gaussianLatticeFourier c hs), hp]
  simp [f, nsmul_eq_mul]

/-- The one-sided cosine series of the Gaussian lattice sum: its positive frequencies, doubled and
scaled by `sqrt (2π) |s|`, sum to `Z(c, s)` minus the zero mode. -/
theorem hasSum_gaussianLatticeCosineSeries (c s : ℝ) :
    HasSum (fun n : ℕ ↦
        2 * sqrt (2 * π) * |s| * rexp (-2 * π ^ 2 * s ^ 2 * (n + 1 : ℝ) ^ 2) *
          cos (2 * π * (n + 1 : ℝ) * c))
      (gaussianLatticeSum c s - sqrt (2 * π) * |s|) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [gaussianLatticeSum_zero_right]
  have h := ((summable_gaussianLatticeFourier c hs).comp_injective
    (i := fun n : ℕ ↦ (n + 1 : ℤ)) fun _ _ h ↦ by simpa using h).hasSum.mul_left
      (2 * sqrt (2 * π) * |s|)
  rw [gaussianLatticeSum_eq_cosineSeries c s]
  push_cast [Function.comp_def] at h
  convert h using 1
  · funext n
    ring
  · ring

/-- The one-sided cosine series of the Gaussian lattice sum converges uniformly in the centre. -/
theorem hasSumUniformly_gaussianLatticeCosineSeries (s : ℝ) :
    HasSumUniformly
      (fun n : ℕ ↦ fun c : ℝ ↦
        2 * sqrt (2 * π) * |s| * rexp (-2 * π ^ 2 * s ^ 2 * (n + 1 : ℝ) ^ 2) *
          cos (2 * π * (n + 1 : ℝ) * c))
      (fun c ↦ gaussianLatticeSum c s - sqrt (2 * π) * |s|) := by
  have hu : Summable fun n : ℕ ↦
      2 * sqrt (2 * π) * |s| * rexp (-2 * π ^ 2 * s ^ 2 * (n + 1 : ℝ) ^ 2) := by
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    have h := ((summable_gaussianLatticeFourierCoeff hs).comp_injective
      (i := fun n : ℕ ↦ (n + 1 : ℤ)) fun _ _ h ↦ by simpa using h).mul_left
        (2 * sqrt (2 * π) * |s|)
    push_cast [Function.comp_def] at h
    exact h
  simp_rw [← (hasSum_gaussianLatticeCosineSeries _ s).tsum_eq, ← hasSumUniformlyOn_univ_iff]
  exact .of_norm_le_summable hu fun _ _ _ ↦
    (norm_mul_le_of_le (norm_of_nonneg (by positivity)).le (abs_cos_le_one _)).trans_eq (mul_one _)

end Real
