/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import TauCeti.NumberTheory.LSeries.GaussianTheta.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import TauCeti.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Poisson summation for positive-index theta series

For periodic coefficients with the parity of the Gaussian weight, the positive-index
sum transforms to the inverse finite Fourier transform at the reciprocal scale. The
constant terms on the two sides must be retained unless the coefficient at zero and the
mean coefficient vanish. For a nonprincipal Dirichlet character they both vanish, so the
large-scale Gaussian bound gives exponential decay at zero without assuming primitivity.
This decay controls the lower endpoint of the Mellin integral.

The normalization is that of `New.gaussianTheta_poisson_summation` in lsernau/grh-lean,
`grh/src/Lib/Analytic/DirichletTheta.lean` at revision `72fead1`. We use
`ZMod.tsum_periodic_gaussian_eq_invDFT`, the bilateral identity from the Hurwitz theta kernels.
-/

public section

open Complex TauCeti
open scoped ZMod

namespace ZMod

variable {N : ℕ} [NeZero N]

local notation "W" j:arg x:arg => ((x ^ j * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ)

/-- When the coefficients and weight have matching parity, the bilateral sum includes the
zero-index term and twice the positive-index theta sum. -/
theorem tsum_periodic_gaussian_eq_gaussianTheta (Φ : ZMod N → ℂ) (j : Fin 2)
    (hΦ : ∀ a, Φ (-a) = (-1 : ℂ) ^ j.val * Φ a) {t : ℝ} (ht : t ≠ 0) :
    (∑' n : ℤ, Φ n * W j.val ((n : ℝ) * t)) =
      Φ 0 * gaussianMonomial j 0 + 2 * gaussianTheta j (fun n ↦ Φ n) t := by
  have hneg (x : ℝ) : W j.val (-x) = (-1 : ℂ) ^ j.val * W j.val x := by
    fin_cases j <;> simp
  have heven : (fun n : ℤ ↦ Φ n * W j.val ((n : ℝ) * t)).Even := by
    intro n
    simp only [Int.cast_neg]
    rw [neg_mul (n : ℝ) t, hΦ, hneg, mul_mul_mul_comm, ← mul_pow]
    simp
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_periodic_gaussian Φ j.val ht),
    gaussianTheta_def]
  fin_cases j <;> simp

/-- The positive-index Poisson identity for periodic coefficients of either parity. Each
half of the corresponding zero-index term is included in the transformed expression. -/
theorem gaussianTheta_eq_invDFT (Φ : ZMod N → ℂ) (j : Fin 2)
    (hΦ : ∀ a, Φ (-a) = (-1 : ℂ) ^ j.val * Φ a) {t : ℝ} (ht : 0 < t) :
    gaussianTheta j (fun n ↦ Φ n) t + Φ 0 * gaussianMonomial j 0 / 2 =
      (-I) ^ j.val / (t : ℂ) *
        (gaussianTheta j (fun n ↦ 𝓕⁻ Φ n) (1 / (N * t)) +
          𝓕⁻ Φ 0 * gaussianMonomial j 0 / 2) := by
  have hdual (a : ZMod N) : 𝓕⁻ Φ (-a) = (-1 : ℂ) ^ j.val * 𝓕⁻ Φ a := by
    have he : (fun b ↦ Φ (-b)) = ((-1 : ℂ) ^ j.val) • Φ := funext hΦ
    have hd := congrFun (dft_comp_neg Φ) (-a)
    rw [he, dft_const_smul, Pi.smul_apply, neg_neg] at hd
    simp only [invDFT_apply', neg_neg, smul_eq_mul]
    rw [← hd, smul_eq_mul, mul_left_comm]
  have hv : 0 < 1 / ((N : ℝ) * t) := one_div_pos.mpr (mul_pos (mod_cast NeZero.pos N) ht)
  have hj : j.val ≤ 1 := Nat.le_of_lt_succ j.isLt
  have h := tsum_periodic_gaussian_eq_invDFT Φ hj ht
  rw [tsum_periodic_gaussian_eq_gaussianTheta Φ j hΦ ht.ne',
    tsum_periodic_gaussian_eq_gaussianTheta (𝓕⁻ Φ) j hdual hv.ne'] at h
  linear_combination h / 2

end ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- For a nonprincipal Dirichlet character, the positive-index Poisson identity has no
zero-index correction, even when the character is imprimitive. -/
theorem gaussianTheta_eq_invDFT (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (j : Fin 2)
    (hj : χ (-1) = (-1 : ℂ) ^ j.val) {t : ℝ} (ht : 0 < t) :
    gaussianTheta j (fun n ↦ χ n) t = (-I) ^ j.val / (t : ℂ) *
      gaussianTheta j (fun n ↦ 𝓕⁻ (χ : ZMod N → ℂ) n) (1 / (N * t)) := by
  have hχ₀ : χ 0 = 0 := χ.map_zero' fun h ↦ hχ (level_one' χ h)
  have hdual₀ : (𝓕⁻ (χ : ZMod N → ℂ)) 0 = 0 := by
    rw [ZMod.invDFT_apply', neg_zero, ZMod.dft_apply_zero, χ.sum_eq_zero_of_ne_one hχ, smul_zero]
  simpa only [hχ₀, hdual₀, zero_mul, zero_div, add_zero] using
    ZMod.gaussianTheta_eq_invDFT χ j (fun a ↦ by rw [← neg_one_mul, map_mul, hj]) ht

/-- At positive scales the unnormalized theta sum of a nonprincipal Dirichlet character is
bounded by `3 N exp(-1 / (N t))`. In particular it decays exponentially as `1/t` tends to
infinity, with no primitivity requirement. -/
theorem norm_gaussianTheta_le_exp_inv (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (j : Fin 2)
    (hj : χ (-1) = (-1 : ℂ) ^ j.val) {t : ℝ} (ht : 0 < t) :
    ‖gaussianTheta j (fun n ↦ χ n) t‖ ≤ 3 * N * Real.exp (-(1 / (N * t))) := by
  have hN : 0 < (N : ℝ) := mod_cast NeZero.pos N
  have hv : 0 < 1 / ((N : ℝ) * t) := one_div_pos.mpr (mul_pos hN ht)
  have hc (n : ℕ+) : ‖𝓕⁻ (χ : ZMod N → ℂ) (n : ℕ)‖ ≤ 1 := by
    rw [ZMod.invDFT_apply, norm_smul, norm_inv, Complex.norm_natCast]
    have hb (a : ZMod N) : ‖ZMod.stdAddChar (a * ((n : ℕ) : ZMod N)) • χ a‖ ≤ 1 := by
      rw [norm_smul, AddChar.norm_apply, one_mul]
      exact χ.norm_le_one a
    have hs := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun a _ ↦ hb a)
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at hs
    exact le_trans (mul_le_mul_of_nonneg_left hs (by positivity)) (by simp [hN.ne'])
  rw [χ.gaussianTheta_eq_invDFT hχ j hj ht, norm_mul, norm_div, norm_pow, norm_neg,
    norm_I, one_pow, norm_real, Real.norm_of_nonneg ht.le, one_div]
  calc
    _ ≤ t⁻¹ * (3 * Real.exp (-(1 / (N * t))) / (1 / (N * t))) :=
      mul_le_mul_of_nonneg_left (norm_gaussianTheta_le hc hv) (by positivity)
    _ = _ := by field_simp

end DirichletCharacter
