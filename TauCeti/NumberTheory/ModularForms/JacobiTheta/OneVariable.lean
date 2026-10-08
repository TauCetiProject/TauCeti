/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Transformation identities of the one-variable Jacobi theta function

Two identities for Mathlib's `jacobiTheta`, `θ(τ) = ∑_n e^{πi n² τ}`, complementing the
transformation laws in `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable`.

## Main results

* `TauCeti.jacobiTheta_sub_natCast_div_two`: splitting `n` by parity,
  `θ(τ - N/2) = e^{-πiN/2} θ(τ) + (1 - e^{-πiN/2}) θ(4τ)` for every natural number `N`.
* `TauCeti.jacobiTheta_I_mul`: the functional equation on the imaginary axis,
  `θ(iy) = θ(i/y) / √y` for `y > 0`.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- Splitting `θ(τ - N/2)` by the parity of `n`: the shift multiplies the even terms by `1` and
the odd terms by `e^{-πiN/2}`, and the even terms alone form `θ(4τ)`. -/
theorem jacobiTheta_sub_natCast_div_two (N : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (τ - N / 2) = cexp (-π * I * N / 2) * jacobiTheta τ +
      (1 - cexp (-π * I * N / 2)) * jacobiTheta (4 * τ) := by
  -- Adding an integer multiple of `2πi` does not change `cexp`.
  have hper (x : ℂ) (k : ℤ) : cexp (x + k * (2 * π * I)) = cexp x := by
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hτ' : 0 < (τ - N / 2).im := by
    rw [sub_im, ← ofReal_natCast, ← ofReal_ofNat, ← ofReal_div, ofReal_im, sub_zero]
    exact hτ
  have hsplit (σ : ℂ) (hσ : 0 < σ.im) : jacobiTheta σ =
      ∑' q : ℤ, jacobiTheta₂_term (2 * q) 0 σ + ∑' q : ℤ, jacobiTheta₂_term (2 * q + 1) 0 σ := by
    rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂,
      tsum_int_eq_sum_fin_tsum ((summable_jacobiTheta₂_term_iff _ _).2 hσ) 2, Fin.sum_univ_two]
    simp [mul_comm]
  -- Even terms see the shift by `-N/2` as a multiple of `2πi`, odd terms as `-πiN/2`.
  have heven (q : ℤ) : jacobiTheta₂_term (2 * q) 0 (τ - N / 2) = jacobiTheta₂_term q 0 (4 * τ) := by
    rw [jacobiTheta₂_term, jacobiTheta₂_term, ← hper _ (q ^ 2 * N)]
    congr 1
    push_cast
    ring
  have hodd (q : ℤ) : jacobiTheta₂_term (2 * q + 1) 0 (τ - N / 2) =
      cexp (-π * I * N / 2) * jacobiTheta₂_term (2 * q + 1) 0 τ := by
    rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add,
      ← hper _ ((q ^ 2 + q) * N)]
    congr 1
    push_cast
    ring
  have h4 : ∑' q : ℤ, jacobiTheta₂_term q 0 (4 * τ) = ∑' q : ℤ, jacobiTheta₂_term (2 * q) 0 τ := by
    refine tsum_congr fun q ↦ ?_
    rw [jacobiTheta₂_term, jacobiTheta₂_term]
    congr 1
    push_cast
    ring
  rw [hsplit _ hτ', hsplit _ hτ, tsum_congr heven, tsum_congr hodd, tsum_mul_left, h4,
    jacobiTheta_eq_jacobiTheta₂ (4 * τ), jacobiTheta₂, h4]
  ring

/-- The functional equation on the imaginary axis: `θ(iy) = θ(i/y) / √y`. -/
theorem jacobiTheta_I_mul {y : ℝ} (hy : 0 < y) :
    jacobiTheta (I * y) = jacobiTheta (I / y) / √y := by
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_functional_equation, jacobiTheta_eq_jacobiTheta₂]
  have h1 : -I * (I * y) = y := by rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  have h2 : -1 / (I * y) = I / y := by field_simp; rw [I_sq]
  have h3 : (y : ℂ) ^ (1 / 2 : ℂ) = (√y : ℝ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow hy.le]
    norm_num
  rw [h1, h2, h3]
  simp [div_eq_inv_mul]

end TauCeti
