/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum
import TauCeti.Analysis.Fourier.Poisson.Periodic
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Poisson summation for Gaussian sums

This file rewrites the shifted Gaussian lattice sum as its Fourier series.  The identity is the
Poisson summation formula for a translated Gaussian and is the analytic bridge from
`Real.gaussianLatticeSum` to periodized Gaussian densities.

For every width `s`,

`Z(c, s) = sqrt (2 * pi) * |s| * sum n, exp (-2 * pi^2 * s^2 * n^2) * cos (2 * pi * n * c)`.

The Fourier series converges absolutely, and uniformly in the centre `c`.  Splitting the integer
sum into its zero term and paired positive and negative terms gives the corresponding one-sided
cosine series used for wrapped normal densities.  The proof specializes Mathlib's
`Complex.tsum_exp_neg_quadratic`.

`ZMod.tsum_periodic_gaussian_eq_invDFT` applies Schwartz Poisson summation with periodic
coefficients to Gaussians of degree zero or one and uses the Fourier transform of a Gaussian
monomial. `ZMod.hasSum_periodic_gaussian_residue_sum` expresses the same input sum through
Mathlib’s Hurwitz theta kernels.

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

open Finset HurwitzZeta
open scoped Real ZMod

local notation "W" j:arg t:arg => ((t ^ j * Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)

namespace ZMod

/-- A Gaussian of positive width times a monomial is summable against periodic coefficients. -/
theorem summable_periodic_gaussian {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    (j : ℕ) {t : ℝ} (ht : t ≠ 0) :
    Summable fun n : ℤ ↦ Φ n * W j ((n : ℝ) * t) := by
  have hsum : Summable fun n : ℤ ↦ |(n : ℝ)| ^ j * Real.exp (-π * (t ^ 2 * (n : ℝ) ^ 2)) := by
    simpa using summable_pow_mul_jacobiTheta₂_term_bound 0 (sq_pos_of_ne_zero ht) j
  obtain ⟨B, hB⟩ := (Set.finite_range (fun a ↦ ‖Φ a‖)).bddAbove
  refine (hsum.mul_left (B * |t| ^ j)).of_norm_bounded fun n ↦ ?_
  have hexp : -π * ((n : ℝ) * t) ^ 2 = -π * (t ^ 2 * (n : ℝ) ^ 2) := by ring
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, mul_pow,
    abs_of_nonneg (Real.exp_pos _).le, hexp]
  have hcoeff := hB (Set.mem_range_self (n : ZMod N))
  refine (mul_le_mul_of_nonneg_right hcoeff (by positivity)).trans_eq ?_
  ring

/-- For degrees zero and one, group a bilateral Gaussian sum with periodic coefficients into
residue classes, expressed using the even or odd Hurwitz theta kernel. -/
theorem hasSum_periodic_gaussian_residue_sum {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    {j : ℕ} (hj : j ≤ 1) {t : ℝ} (ht : t ≠ 0) :
    HasSum (fun n : ℤ ↦ Φ n * W j ((n : ℝ) * t))
      (((N : ℝ) * t : ℂ) ^ j * ∑ a : ZMod N, Φ a *
        ((if j = 0 then evenKernel else oddKernel) (toAddCircle a) (((N : ℝ) * t) ^ 2) : ℂ)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsq : 0 < ((N : ℝ) * t) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hN ht)
  have hsummable := summable_periodic_gaussian Φ j ht
  convert hsummable.hasSum using 1
  symm
  rw [hsummable.tsum_int_eq_sum_zmod_tsum N, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  have hcast (n : ℤ) : ((n * N + (a.val : ℤ) : ℤ) : ZMod N) = a := by simp
  have hs (n : ℤ) : (n + (a.val / (N : ℝ))) * (N * t) =
      ((n * (N : ℤ) + (a.val : ℤ) : ℤ) : ℝ) * t := by
    push_cast
    field_simp
  simp only [hcast, toAddCircle_apply]
  interval_cases j
  · simp only [pow_zero, ite_true, one_mul]
    rw [← (hasSum_ofReal.mpr (hasSum_int_evenKernel (a.val / (N : ℝ)) hsq)).tsum_eq,
      ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [← hs n, mul_pow, ofReal_exp]
    simp [mul_assoc]
  · simp only [pow_one, one_ne_zero, ite_false]
    rw [← (hasSum_ofReal.mpr (hasSum_int_oddKernel (a.val / (N : ℝ)) hsq)).tsum_eq,
      ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [← hs n, mul_pow]
    push_cast
    simp [mul_assoc, mul_left_comm, mul_comm]

open scoped SchwartzMap FourierTransform

/-- Poisson summation for a periodic Gaussian sum of degree zero or one. The inverse finite
Fourier transform includes the factor `1 / N`; degree one has the additional factor `−i`. -/
theorem tsum_periodic_gaussian_eq_invDFT {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    {j : ℕ} (hj : j ≤ 1) {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, Φ n * W j ((n : ℝ) * t)) =
      (-(I : ℂ)) ^ j / (t : ℂ) *
        ∑' n : ℤ, dft.symm Φ n * W j ((n : ℝ) * (1 / (N * t))) := by
  have hb : 0 < (π : ℂ).re := Real.pi_pos
  let f : 𝓢(ℝ, ℂ) := if j = 0 then SchwartzMap.gaussian hb else SchwartzMap.innerMulGaussian hb 1
  have hw (x : ℝ) : W j x = (x : ℂ) ^ j * cexp (-(π : ℂ) * ‖x‖ ^ 2) := by
    simp only [ofReal_mul, ofReal_exp, ofReal_neg, Real.norm_eq_abs, ← ofReal_pow, sq_abs]
  have hf (x : ℝ) : f x = W j x := by
    rw [hw]
    by_cases h : j = 0
    · simp only [f, ite_eq_left h, SchwartzMap.gaussian_apply, h, pow_zero, one_mul]
    · have h₁ : j = 1 := by lia
      simp only [f, ite_eq_right h, SchwartzMap.innerMulGaussian_apply,
        h₁, pow_one, Real.inner_apply,
        mul_one]
  have hfourier (x : ℝ) : (𝓕 f) x = (-I) ^ j * W j x := by
    rw [SchwartzMap.fourier_coe, funext hf, funext hw,
      TauCeti.fourier_pow_mul_cexp_neg_mul_norm_sq_real hb hj]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have harg : -(π : ℂ) ^ 2 * ‖x‖ ^ 2 / π = -(π : ℂ) * ‖x‖ ^ 2 := by field_simp
    -- The normalized Gaussian has parameter `π` on both sides, so the power factor is one.
    rw [div_self hπ, one_cpow, one_mul, harg, hw, mul_assoc]
  have h := (f.dilate ht.ne').tsum_mul_periodic_eq_tsum_invDFT_fourier Φ
  -- Substitute the Gaussian transform and express real dilations by division.
  simp_rw [SchwartzMap.dilate_apply, SchwartzMap.fourier_dilate_apply, hfourier, hf,
    Module.finrank_self, pow_one, Complex.real_smul, abs_of_pos ht, ofReal_inv,
    smul_eq_mul, ← div_eq_inv_mul] at h
  calc
    _ = ∑' n : ℤ, Φ n * W j (t * (n : ℝ)) := tsum_congr fun n ↦ by rw [mul_comm t]
    _ = _ := h.trans ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [div_div, div_eq_mul_one_div ((n : ℝ))]
  ring

end ZMod
