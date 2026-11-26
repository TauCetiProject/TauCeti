/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Inversion of periodic Gaussian theta sums

Poisson summation exchanges a periodic coefficient function with its inverse finite Fourier
transform. For primitive Dirichlet characters the Gauss sum then gives an absolute-value
inversion formula. This symmetry permits folding the Mellin integral on the critical line at
the inverse square root of the conductor.

The normalization of the absolute-value formula is that of `New.norm_thetaSeries_inv` in
`grh/src/Lib/Analytic/DirichletTheta.lean` of `lsernau/grh-lean` (revision `72fead1`). The proofs
below use Mathlib's even and odd Hurwitz theta kernels.
-/

public section

open Complex Finset HurwitzZeta
open scoped ComplexConjugate Real ZMod

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
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, mul_pow,
    abs_of_nonneg (Real.exp_pos _).le,
    show (-π * ((n : ℝ) * t) ^ 2) = -π * (t ^ 2 * (n : ℝ) ^ 2) by ring]
  have hcoeff := hB (Set.mem_range_self (n : ZMod N))
  refine (mul_le_mul_of_nonneg_right hcoeff (by positivity)).trans_eq ?_
  ring

private theorem tsum_periodic_gaussian_eq_residue_sum {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    {j : ℕ} (hj : j ≤ 1) {t : ℝ} (ht : t ≠ 0) :
    (∑' n : ℤ, Φ n * W j ((n : ℝ) * t)) =
      ((N : ℝ) * t : ℂ) ^ j * ∑ a : ZMod N, Φ a *
        (if j = 0 then (evenKernel (toAddCircle a) (((N : ℝ) * t) ^ 2) : ℂ)
          else (oddKernel (toAddCircle a) (((N : ℝ) * t) ^ 2) : ℂ)) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsq : 0 < ((N : ℝ) * t) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hN ht)
  rw [TauCeti.tsum_int_eq_sum_fin_tsum (summable_periodic_gaussian Φ j ht) N]
  rw [mul_sum, ← (finEquiv N).toEquiv.sum_comp]
  have hfin (a : Fin N) : (finEquiv N).toEquiv a = (a.val : ZMod N) := finEquiv_apply a
  simp only [hfin]
  refine sum_congr rfl fun a _ ↦ ?_
  have hcast (n : ℤ) : ((n * N + (a : ℤ) : ℤ) : ZMod N) = (a.val : ZMod N) := by simp
  have hs (n : ℤ) : (n + ((a : ℕ) / (N : ℝ))) * (N * t) =
      ((n * (N : ℤ) + (a : ℤ) : ℤ) : ℝ) * t := by
    push_cast
    field_simp
  simp only [hcast, toAddCircle_apply, val_cast_of_lt a.isLt]
  interval_cases j
  · simp only [pow_zero, ite_true, one_mul]
    rw [← (hasSum_ofReal.mpr (hasSum_int_evenKernel ((a : ℕ) / (N : ℝ)) hsq)).tsum_eq,
      ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [← hs n, mul_pow, ofReal_exp]
    simp [mul_assoc]
  · simp only [pow_one, one_ne_zero, ite_false]
    rw [← (hasSum_ofReal.mpr (hasSum_int_oddKernel ((a : ℕ) / (N : ℝ)) hsq)).tsum_eq,
      ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [← hs n, mul_pow]
    push_cast
    simp [mul_assoc, mul_left_comm, mul_comm]

private theorem exp_eq_stdAddChar_mul_intCast {N : ℕ} [NeZero N] (a : ZMod N) (n : ℤ) :
    exp (2 * π * I * ((a.val : ℝ) / N : ℝ) * n) = stdAddChar (a * (n : ZMod N)) := by
  have h : a * (n : ZMod N) = (((a.val : ℤ) * n : ℤ) : ZMod N) := by simp
  rw [h, stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem hasSum_weighted_fourier_kernel {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    {j : ℕ} (hj : j ≤ 1) {y : ℝ} (hy : y ≠ 0) :
    HasSum (fun n : ℤ ↦ (-(I : ℂ)) ^ j * (n : ℂ) ^ j *
      (N : ℂ) * (𝓕⁻ Φ) n * Real.exp (-Real.pi * (n : ℝ) ^ 2 * y ^ 2))
      (∑ a : ZMod N, Φ a * if j = 0 then (cosKernel (toAddCircle a) (y ^ 2) : ℂ)
        else (sinKernel (toAddCircle a) (y ^ 2) : ℂ)) := by
  have hy2 := sq_pos_of_ne_zero hy
  have hk (a : ZMod N) : HasSum (fun n : ℤ ↦ (-(I : ℂ)) ^ j * (n : ℂ) ^ j *
      stdAddChar (a * (n : ZMod N)) * Real.exp (-Real.pi * (n : ℝ) ^ 2 * y ^ 2))
      (if j = 0 then (cosKernel (toAddCircle a) (y ^ 2) : ℂ)
        else (sinKernel (toAddCircle a) (y ^ 2) : ℂ)) := by
    rw [toAddCircle_apply]
    simp_rw [← exp_eq_stdAddChar_mul_intCast]
    interval_cases j
    · simpa using hasSum_int_cosKernel ((a.val : ℝ) / N) hy2
    · simpa using hasSum_int_sinKernel ((a.val : ℝ) / N) hy2
  refine (hasSum_sum (s := univ) fun a _ ↦ (hk a).mul_left (Φ a)).congr_fun fun n ↦ ?_
  rw [invDFT_apply]
  simp only [smul_eq_mul]
  rw [mul_assoc (_ * _) (↑N : ℂ), ← mul_assoc (↑N : ℂ), mul_inv_cancel₀ (NeZero.ne (N : ℂ)),
    one_mul, mul_sum, sum_mul]
  refine sum_congr rfl fun _ _ ↦ ?_
  ring

/-- Poisson summation for a periodic Gaussian sum of degree zero or one. The inverse finite
Fourier transform includes the factor `1 / N`; degree one has the additional factor `−i`. -/
theorem tsum_periodic_gaussian_eq_invDFT {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ)
    {j : ℕ} (hj : j ≤ 1) {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, Φ n * W j ((n : ℝ) * t)) =
      (-(I : ℂ)) ^ j / (t : ℂ) *
        ∑' n : ℤ, (𝓕⁻ Φ) n * W j ((n : ℝ) * (1 / (N * t))) := by
  let y : ℝ := 1 / (N * t)
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hy : 0 < y := one_div_pos.mpr (mul_pos hN ht)
  have hi : 1 / ((N : ℝ) * t) ^ 2 = y ^ 2 := by dsimp [y]; rw [div_pow, one_pow]
  have hsqr : (((N : ℝ) * t) ^ 2) ^ (1 / 2 : ℝ) = N * t := by
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  have hcub : (((N : ℝ) * t) ^ 2) ^ (3 / 2 : ℝ) = ((N : ℝ) * t) ^ 3 := by
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  have hkernel (a : ZMod N) :
      (if j = 0 then (evenKernel (toAddCircle a) (((N : ℝ) * t) ^ 2) : ℂ)
        else (oddKernel (toAddCircle a) (((N : ℝ) * t) ^ 2) : ℂ)) =
      ((y : ℂ) ^ (2 * j + 1)) *
        (if j = 0 then (cosKernel (toAddCircle a) (y ^ 2) : ℂ)
          else (sinKernel (toAddCircle a) (y ^ 2) : ℂ)) := by
    interval_cases j
    · simp only [ite_true, evenKernel_functional_equation, hi, hsqr, ofReal_mul,
        Nat.mul_zero, zero_add, pow_one, y]
    · rw [ite_eq_right Nat.one_ne_zero, ite_eq_right Nat.one_ne_zero,
        oddKernel_functional_equation, hi, hcub, ofReal_mul, ← ofReal_pow]
      congr 1
      exact congrArg ofReal (by simpa only [y, one_pow] using
        (div_pow (1 : ℝ) ((N : ℝ) * t) 3).symm)
  -- Pass from the residue classes to the dual integer sum using the kernel identities.
  rw [tsum_periodic_gaussian_eq_residue_sum Φ hj ht.ne']
  simp_rw [hkernel, mul_left_comm (Φ _), ← mul_sum,
    ← (hasSum_weighted_fourier_kernel Φ hj hy.ne').tsum_eq]
  simp_rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  simp only [mul_pow, ofReal_mul, ofReal_pow, ofReal_intCast, y, ofReal_div, ofReal_one,
    ofReal_natCast]
  have hNc : (N : ℂ) ≠ 0 := NeZero.ne _
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  interval_cases j <;> norm_num <;> field_simp [hNc, htc]

end ZMod

namespace DirichletCharacter

private theorem tsum_gaussian_eq_two_mul_tsum_succ {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ₀ : χ 0 = 0) {j : ℕ} (hpar : χ (-1) = (-1) ^ j)
    {t : ℝ} (ht : t ≠ 0) :
    (∑' n : ℤ, χ n * W j ((n : ℝ) * t)) =
      2 * ∑' n : ℕ, χ (n + 1 : ℕ) * W j ((n + 1 : ℕ) * t) := by
  have heven : (fun n : ℤ ↦ χ n * W j ((n : ℝ) * t)).Even := by
    intro n
    have hw (x : ℝ) : W j (-x) = (-1 : ℂ) ^ j * W j x := by
      rw [neg_pow x, neg_sq, mul_assoc, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one]
    dsimp only
    rw [Int.cast_neg, Int.cast_neg, neg_mul, hw,
      ← neg_one_mul (n : ZMod N), map_mul, hpar, mul_mul_mul_comm,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven (ZMod.summable_periodic_gaussian χ j ht)]
  simp only [Int.cast_zero, hχ₀, zero_mul, zero_add, two_nsmul, ← two_mul,
    Int.cast_natCast]
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
  rw [tsum_gaussian_eq_two_mul_tsum_succ χ (χ.map_zero' hq) hpar ht.ne',
    tsum_gaussian_eq_two_mul_tsum_succ χ (χ.map_zero' hq) hpar hy.ne',
    norm_mul, norm_mul, Complex.norm_two, mul_left_comm ((Real.sqrt N * t)⁻¹),
    mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0)] at h
  rw [h, ← mul_assoc, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    Real.sqrt_mul hN.le]
  congr 1
  have hs := Real.sq_sqrt ht.le
  field_simp [Real.sqrt_pos.mpr hN, Real.sqrt_pos.mpr ht, ht.ne']
  nlinarith

end DirichletCharacter
