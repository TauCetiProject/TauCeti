/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Inversion of Dirichlet theta sums

Poisson summation exchanges a periodic coefficient function with its inverse finite Fourier
transform. For primitive Dirichlet characters the Gauss sum then gives an absolute-value
inversion formula. This symmetry permits folding the Mellin integral on the critical line at
the inverse square root of the conductor.

The normalization of the absolute-value formula is that of `New.norm_thetaSeries_inv` in
`grh/src/Lib/Analytic/DirichletTheta.lean` of `lsernau/grh-lean` (revision `72fead1`). The
Poisson formula used here comes from Mathlib's even and odd Hurwitz theta kernels.
-/

public section

open Complex
open scoped ComplexConjugate Real ZMod

local notation "W" j:arg t:arg => ((t ^ j * Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)

namespace DirichletCharacter

/-- For a Gaussian weight of matching parity, the bilateral sum of a character is its zero
term plus twice the positive-index sum. -/
theorem tsum_gaussian_eq_add_two_mul_tsum_succ {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {j : ℕ} (hpar : χ (-1) = (-1) ^ j)
    {t : ℝ} (ht : t ≠ 0) :
    (∑' n : ℤ, χ n * W j ((n : ℝ) * t)) =
      χ 0 * W j (0 : ℝ) + 2 * ∑' n : ℕ, χ (n + 1 : ℕ) * W j ((n + 1 : ℕ) * t) := by
  have heven : (fun n : ℤ ↦ χ n * W j ((n : ℝ) * t)).Even := by
    intro n
    have hw (x : ℝ) : W j (-x) = (-1 : ℂ) ^ j * W j x := by
      rw [neg_pow x, neg_sq, mul_assoc, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one]
    have hχneg : χ (-(n : ZMod N)) = (-1 : ℂ) ^ j * χ n := by
      rw [← neg_one_mul (n : ZMod N), map_mul, hpar]
    have hsign : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
      rw [← mul_pow]
      simp
    simp only [Int.cast_neg]
    rw [neg_mul (n : ℝ) t, hw, hχneg]
    calc
      _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * (χ n * W j ((n : ℝ) * t)) := by ring
      _ = _ := by rw [hsign, one_mul]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven (ZMod.summable_periodic_gaussian χ j ht)]
  simp only [Int.cast_zero, zero_mul, two_nsmul, ← two_mul, Int.cast_natCast]
  rw [← tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ χ n * W j ((n : ℝ) * t))]

private theorem norm_tsum_gaussian_eq_norm_tsum_inv {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {j : ℕ} (hj : j ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    ‖∑' n : ℤ, χ n * W j ((n : ℝ) * t)‖ =
      (Real.sqrt N * t)⁻¹ * ‖∑' n : ℤ, χ n * W j ((n : ℝ) * (1 / (N * t)))‖ := by
  have hDFT (n : ℤ) : (𝓕⁻ (χ : ZMod N → ℂ)) n =
      ((N : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar) * conj (χ n) := by
    rw [ZMod.invDFT_apply', hχ.fourierTransform_eq_inv_mul_gaussSum]
    simp only [neg_neg, smul_eq_mul]
    rw [← MulChar.star_apply', Complex.star_def]
    ring
  have hconj : (∑' n : ℤ, conj (χ n) * W j ((n : ℝ) * (1 / (N * t)))) =
      conj (∑' n : ℤ, χ n * W j ((n : ℝ) * (1 / (N * t)))) := by
    simp only [conj_tsum, map_mul, conj_ofReal]
  rw [ZMod.tsum_periodic_gaussian_eq_invDFT χ hj ht]
  simp_rw [hDFT, mul_assoc ((N : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar)]
  rw [tsum_mul_left, hconj, norm_mul, norm_mul, norm_conj, ← mul_assoc]
  congr 1
  simp only [norm_div, norm_pow, norm_neg, norm_I, one_pow,
    norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_inv, norm_mul, Complex.norm_natCast,
    χ.norm_gaussSum_stdAddChar hχ]
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hs := Real.sq_sqrt hN.le
  field_simp [Real.sqrt_pos.mpr hN, ht.ne', hN.ne']
  nlinarith

/-- The norm of the positive-index theta sum of a primitive nonprincipal character, with
weight `t^(1/2) (nt)^j exp(-π(nt)²)` for its parity `j`, is invariant under `t ↦ 1 / (N * t)`. -/
theorem IsPrimitive.norm_gaussian_theta_inversion {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1)
    {j : ℕ} (hj : j ≤ 1) (hpar : χ (-1) = (-1) ^ j) (t : ℝ) :
    Real.sqrt t * ‖∑' n : ℕ, χ (n + 1 : ℕ) * W j ((n + 1 : ℕ) * t)‖ =
      Real.sqrt (1 / (N * t)) *
        ‖∑' n : ℕ, χ (n + 1 : ℕ) * W j ((n + 1 : ℕ) * (1 / (N * t)))‖ := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  rcases le_or_gt t 0 with ht | ht
  · rw [Real.sqrt_eq_zero_of_nonpos ht, Real.sqrt_eq_zero_of_nonpos
      (one_div_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos hN.le ht)), zero_mul, zero_mul]
  -- The missing term at zero vanishes, so the bilateral sum is twice the positive sum.
  have hq : N ≠ 1 := fun h ↦ hχ₀ (level_one' χ h)
  have hy : 0 < 1 / ((N : ℝ) * t) := one_div_pos.mpr (mul_pos hN ht)
  have h := norm_tsum_gaussian_eq_norm_tsum_inv hχ hj ht
  rw [tsum_gaussian_eq_add_two_mul_tsum_succ χ hpar ht.ne',
    tsum_gaussian_eq_add_two_mul_tsum_succ χ hpar hy.ne'] at h
  simp only [χ.map_zero' hq, zero_mul, zero_add, norm_mul, Complex.norm_two] at h
  rw [mul_left_comm ((Real.sqrt N * t)⁻¹),
    mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0)] at h
  rw [h, ← mul_assoc, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    Real.sqrt_mul hN.le]
  congr 1
  have hs := Real.sq_sqrt ht.le
  field_simp [Real.sqrt_pos.mpr hN, Real.sqrt_pos.mpr ht, ht.ne']
  nlinarith

end DirichletCharacter
