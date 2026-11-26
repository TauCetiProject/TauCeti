/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import TauCeti.NumberTheory.LSeries.GaussianTheta.Basic

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Inversion of Dirichlet theta series

For a nonprincipal primitive Dirichlet character the norm of the parity-matched normalized Gaussian
series is invariant under `u ↦ 1 / (N * u)`. This lets one estimate the small-scale
part of a Mellin integral using only the large-scale theta tail.

The proof uses the classical theta transformation (Montgomery and Vaughan,
*Multiplicative Number Theory I*, chapter 10), with Mathlib's even and odd Hurwitz
kernel functional equations providing Poisson summation on each residue class.
-/

public section

open Complex Finset MulChar
open scoped Real ComplexConjugate
open TauCeti

namespace TauCeti

/-- Poisson summation for the parity-weighted Gaussian on a shifted integer lattice. -/
theorem hasSum_gaussianMonomial_add_mul (j : Fin 2) (a : ℝ) {v : ℝ} (hv : 0 < v) :
    HasSum (fun n : ℤ ↦ (gaussianMonomial j ((n + a) * v) : ℂ))
      ((v : ℂ)⁻¹ * (-I) ^ j.val *
        ∑' n : ℤ, exp (2 * π * I * a * n) * gaussianMonomial j (n * v⁻¹)) := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hi : 0 < 1 / v ^ 2 := by positivity
  have hp₁ : (v ^ 2) ^ (1 / 2 : ℝ) = v := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hv.le]
  have hp₃ : (v ^ 2) ^ (3 / 2 : ℝ) = v ^ 3 := by
    have hsplit : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [hsplit, Real.rpow_add hv2, Real.rpow_one, hp₁]
    ring
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  · have h₁ := hasSum_ofReal.mpr (HurwitzZeta.hasSum_int_evenKernel a hv2)
    have h₂ := HurwitzZeta.hasSum_int_cosKernel a hi
    rw [HurwitzZeta.evenKernel_functional_equation, hp₁, one_div, ofReal_mul, ofReal_inv,
      ← h₂.tsum_eq] at h₁
    simp only [Fin.val_zero, pow_zero, mul_one]
    convert h₁ using 1
    · funext n
      simp [mul_pow, mul_assoc]
    · congr 1
      exact tsum_congr fun n ↦ by simp [mul_pow, div_eq_mul_inv, mul_assoc]
  · have h₁ := (hasSum_ofReal.mpr (HurwitzZeta.hasSum_int_oddKernel a hv2)).mul_left (v : ℂ)
    have h₂ := HurwitzZeta.hasSum_int_sinKernel a hi
    rw [HurwitzZeta.oddKernel_functional_equation, hp₃, one_div, ofReal_mul, ofReal_inv,
      ← h₂.tsum_eq] at h₁
    convert h₁ using 1
    · funext n
      simp only [gaussianMonomial_one, mul_pow, ofReal_mul]
      ac_rfl
    · simp only [Fin.val_one, pow_one, ← tsum_mul_left]
      refine tsum_congr fun n ↦ ?_
      rw [gaussianMonomial_one, mul_pow, inv_pow, ← div_eq_mul_inv]
      push_cast
      field_simp

/-- A bounded sequence times the parity-weighted Gaussian is summable on `ℤ`. -/
theorem summable_mul_gaussianMonomial_int (j : Fin 2) {u : ℝ} (hu : 0 < u)
    (c : ℤ → ℂ) {C : ℝ} (hc : ∀ n, ‖c n‖ ≤ C) :
    Summable (fun n : ℤ ↦ c n * gaussianMonomial j (n * u)) := by
  have h := (hasSum_gaussianMonomial_add_mul j 0 hu).summable.norm.mul_left C
  refine Summable.of_norm (h.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_)
  simpa only [norm_mul, add_zero] using
    mul_le_mul_of_nonneg_right (hc n) (norm_nonneg (gaussianMonomial j (n * u) : ℂ))

end TauCeti

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
private theorem tsum_int_gaussianChar (χ : DirichletCharacter ℂ N) (j : Fin 2)
    (hpar : χ (-1) = (-1 : ℂ) ^ j.val) {u : ℝ} (hu : 0 < u) (hzero : χ 0 = 0) :
    (∑' n : ℤ, χ n * gaussianMonomial j (n * u)) =
      2 * gaussianTheta j (fun n : ℕ ↦ χ n) u := by
  have hs := summable_mul_gaussianMonomial_int j hu (fun n ↦ χ n) (fun n ↦ χ.norm_le_one n)
  have hneg (x : ℝ) : gaussianMonomial j (-x) = (-1) ^ j.val * gaussianMonomial j x := by
    fin_cases j <;> simp [neg_mul]
  have he : Function.Even (fun n : ℤ ↦ χ n * (gaussianMonomial j (n * u) : ℂ)) := by
    intro n
    simp only [Int.cast_neg, neg_mul, hneg, ofReal_mul, ofReal_pow, ofReal_neg,
      ofReal_one]
    rw [← neg_one_mul (n : ZMod N), map_mul, hpar, mul_comm _ (χ _), mul_assoc,
      ← mul_assoc ((-1 : ℂ) ^ j.val), ← mul_pow]
    simp
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat he hs, gaussianTheta_def]
  simp [hzero, two_mul]

-- Sum the Fourier side over residue classes before evaluating the Gauss sums.
private theorem sum_mul_tsum_gaussian_eq_gaussSum_mul (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (j : Fin 2) {v : ℝ} (hv : 0 < v) (z : ℂ) :
    (∑ a : ZMod N, χ a * (z * ∑' n : ℤ,
      exp (2 * π * I * (a.val / (N : ℝ) : ℝ) * n) * gaussianMonomial j (n * v))) =
      z * gaussSum χ ZMod.stdAddChar * ∑' n : ℤ, χ⁻¹ n * gaussianMonomial j (n * v) := by
  let c (a : ZMod N) (n : ℤ) := χ a * exp (2 * π * I * (a.val / (N : ℝ) : ℝ) * n)
  let w (n : ℤ) : ℂ := gaussianMonomial j (n * v)
  have hc (a : ZMod N) (n : ℤ) : ‖c a n‖ ≤ 1 := by
    simpa [c, norm_mul, Complex.norm_exp, mul_re, mul_im] using χ.norm_le_one a
  calc
    _ = ∑ a : ZMod N, z * ∑' n : ℤ, c a n * w n := by
      refine sum_congr rfl fun a _ ↦ ?_
      simp only [c, mul_assoc (χ a), tsum_mul_left]
      ring
    _ = _ := by
      rw [← mul_sum, mul_assoc z]
      congr 1
      rw [← Summable.tsum_finsetSum (fun a _ ↦
        summable_mul_gaussianMonomial_int j hv _ (hc a)), ← tsum_mul_left]
      refine tsum_congr fun n ↦ ?_
      have hsum : (∑ a, c a n) = gaussSum χ (ZMod.stdAddChar.mulShift (n : ZMod N)) := by
        rw [gaussSum]
        refine sum_congr rfl fun a _ ↦ ?_
        simp only [c, AddChar.mulShift_apply, mul_comm (n : ZMod N)]
        rw [← ZMod.fourier_val_div_eq_stdAddChar, fourier_coe_apply, ofReal_one, div_one,
          mul_right_comm]
      rw [← sum_mul, hsum, gaussSum_mulShift_of_isPrimitive _ hχ]
      ring

private theorem gaussianTheta_int_functional_equation (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (j : Fin 2) {u : ℝ} (hu : 0 < u) :
    (∑' n : ℤ, χ n * gaussianMonomial j (n * u)) =
      (((N : ℝ) * u : ℝ) : ℂ)⁻¹ * (-I) ^ j.val * gaussSum χ ZMod.stdAddChar *
        ∑' n : ℤ, χ⁻¹ n * gaussianMonomial j (n * ((N : ℝ) * u)⁻¹) := by
  let v : ℝ := (N : ℝ) * u
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hv : 0 < v := mul_pos hN hu
  let f : ℤ → ℂ := fun n ↦ χ n * gaussianMonomial j (n * u)
  have hs : Summable f :=
    summable_mul_gaussianMonomial_int j hu (fun n ↦ χ n) (fun n ↦ χ.norm_le_one n)
  calc
    ∑' n : ℤ, f n = ∑ a : ZMod N, ∑' n : ℤ, f (n * N + a.val) := by
      rw [tsum_int_eq_sum_fin_tsum hs N, ← (ZMod.finEquiv N).toEquiv.sum_comp]
      exact sum_congr rfl fun a _ ↦ by
        simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, ZMod.finEquiv_apply,
          ZMod.val_natCast_of_lt a.isLt]
    _ = ∑ a : ZMod N, χ a * ((v : ℂ)⁻¹ * (-I) ^ j.val *
        ∑' n : ℤ, exp (2 * π * I * (a.val / (N : ℝ) : ℝ) * n) *
          gaussianMonomial j (n * v⁻¹)) := by
      refine sum_congr rfl fun a _ ↦ ?_
      rw [← ((hasSum_gaussianMonomial_add_mul j (a.val / (N : ℝ)) hv).mul_left (χ a)).tsum_eq]
      refine tsum_congr fun n ↦ ?_
      simp only [f, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        zero_add, ZMod.natCast_zmod_val]
      congr 2
      dsimp [v]
      field_simp
    _ = (v : ℂ)⁻¹ * (-I) ^ j.val * gaussSum χ ZMod.stdAddChar *
        ∑' n : ℤ, χ⁻¹ n * gaussianMonomial j (n * v⁻¹) :=
      sum_mul_tsum_gaussian_eq_gaussSum_mul χ hχ j (inv_pos.mpr hv) _

/-- The normalized theta series of a nonprincipal primitive character, with matching
parity, has the same norm at `u` and `1 / (N * u)`. Both sides vanish if `u ≤ 0`. -/
theorem norm_gaussianThetaSeries_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχ₁ : χ ≠ 1) (j : Fin 2) (hpar : χ (-1) = (-1 : ℂ) ^ j.val) (u : ℝ) :
    ‖gaussianThetaSeries j (fun n : ℕ ↦ χ n) ((N * u)⁻¹)‖ =
      ‖gaussianThetaSeries j (fun n : ℕ ↦ χ n) u‖ := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rcases le_or_gt u 0 with hu | hu
  · have hnu : ((N : ℝ) * u)⁻¹ ≤ 0 := inv_nonpos.mpr (mul_nonpos_of_nonneg_of_nonpos hN.le hu)
    rw [gaussianThetaSeries_def, gaussianThetaSeries_def, Real.sqrt_eq_zero_of_nonpos hu,
      Real.sqrt_eq_zero_of_nonpos hnu]
    simp
  have hN₁ : N ≠ 1 := fun h ↦ hχ₁ (χ.level_one' h)
  have hv : 0 < (N : ℝ) * u := mul_pos hN hu
  have hpar' : χ⁻¹ (-1) = (-1 : ℂ) ^ j.val := by
    rw [← MulChar.star_apply', hpar]
    simp
  have h := gaussianTheta_int_functional_equation χ hχ j hu
  rw [tsum_int_gaussianChar χ j hpar hu (χ.map_zero' hN₁),
    tsum_int_gaussianChar χ⁻¹ j hpar' (inv_pos.mpr hv) (χ⁻¹.map_zero' hN₁)] at h
  simp only [← MulChar.star_apply', Complex.star_def, gaussianTheta_conj] at h
  have hn := congrArg norm h
  have hnorm : ‖((N * u : ℝ) : ℂ)‖ = N * u := Complex.norm_of_nonneg hv.le
  simp only [norm_mul, norm_inv, hnorm, norm_pow, norm_neg, norm_I, one_pow, mul_one,
    norm_gaussSum_stdAddChar hχ, norm_conj, norm_ofNat] at hn
  have hraw : ‖gaussianTheta j (fun n : ℕ ↦ χ n) u‖ = (N * u)⁻¹ * √(N : ℝ) *
      ‖gaussianTheta j (fun n : ℕ ↦ χ n) ((N * u)⁻¹)‖ := by linarith only [hn]
  simp only [gaussianThetaSeries_def, norm_mul, norm_real, Real.norm_eq_abs,
    Real.sqrt_inv, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), hraw]
  suffices (√((N : ℝ) * u))⁻¹ = √u * ((N * u)⁻¹ * √(N : ℝ)) by rw [this, mul_assoc]
  rw [Real.sqrt_mul hN.le]
  field_simp [hN.ne', hu.ne', (Real.sqrt_pos.mpr hN).ne', (Real.sqrt_pos.mpr hu).ne']
  rw [Real.sq_sqrt hN.le, Real.sq_sqrt hu.le]

end DirichletCharacter
