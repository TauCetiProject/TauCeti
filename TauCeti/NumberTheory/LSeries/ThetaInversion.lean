/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.NumberTheory.LSeries.GaussianTheta.Poisson

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

open Complex TauCeti
open scoped ComplexConjugate Real ZMod

local notation "W" j:arg t:arg => ((t ^ j * Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)

namespace DirichletCharacter

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
  let k : Fin 2 := ⟨j, by omega⟩
  have hk (u : ℝ) : gaussianTheta k (fun n ↦ χ n) u =
      ∑' n : ℕ, χ (n + 1 : ℕ) * W j ((n + 1 : ℕ) * u) := by
    rw [gaussianTheta_def, ← tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ ↦ χ n * W j ((n : ℝ) * u))]
    refine tsum_congr fun n ↦ ?_
    interval_cases j <;> simp [k]
  rw [← hk, ← hk, χ.gaussianTheta_eq_invDFT hχ₀ k hpar ht]
  have hDFT (n : ℕ) : (𝓕⁻ (χ : ZMod N → ℂ)) n =
      ((N : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar) * conj (χ n) := by
    rw [ZMod.invDFT_apply', hχ.fourierTransform_eq_inv_mul_gaussSum]
    simp only [neg_neg, smul_eq_mul, ← MulChar.star_apply', Complex.star_def]
    ring
  let v := 1 / ((N : ℝ) * t)
  have hconj : (∑' n : ℕ+, conj (χ (n : ℕ)) * gaussianMonomial k (n * v)) =
      conj (∑' n : ℕ+, χ (n : ℕ) * gaussianMonomial k (n * v)) := by
    simp only [conj_tsum, map_mul, conj_ofReal]
  rw [gaussianTheta_def, gaussianTheta_def]
  simp_rw [hDFT, mul_assoc ((N : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar)]
  rw [tsum_mul_left, hconj]
  simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_I, one_pow, norm_real,
    Real.norm_eq_abs, abs_of_pos ht, norm_inv, Complex.norm_natCast, norm_conj,
    χ.norm_gaussSum_stdAddChar hχ, Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_mul hN.le]
  simp only [v, ← mul_assoc]
  congr 1
  have ht₂ := Real.sq_sqrt ht.le
  have hN₂ := Real.sq_sqrt hN.le
  field_simp [Real.sqrt_pos.mpr hN, Real.sqrt_pos.mpr ht, ht.ne', hN.ne']
  nlinarith

end DirichletCharacter
