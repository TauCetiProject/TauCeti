/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.Data.Nat.Choose.Cast
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Kummer's transformation of the regularized confluent hypergeometric function

Write `𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z = ∑ (a)ₙ zⁿ / (n! Γ(b + n))` for Olver's
regularized Kummer function. Kummer's transformation (DLMF 13.2.39) states

`𝐌(a, b, z) = e^z 𝐌(b − a, b, −z)`

for all complex `a`, `b`, `z`. Because `1 / Γ` vanishes at the poles of `Γ`, no hypothesis on `b`
is needed.

The proof multiplies the power series of `e^z` and `𝐌(b − a, b, −z)`. With
`(Γ(b + k))⁻¹ = (b + k)ₙ₋ₖ (Γ(b + n))⁻¹`, valid at the poles too, the `n`-th Cauchy coefficient
is `∑ₖ (−1)ᵏ C(n, k) (b − a)ₖ (b + k)ₙ₋ₖ / (n! Γ(b + n))`. The Chu–Vandermonde identity
`TauCeti.sum_neg_one_pow_mul_choose_ascPochhammer` evaluates the numerator sum
`∑ₖ (−1)ᵏ C(n, k) (b − a)ₖ (b + k)ₙ₋ₖ` as `(a)ₙ`, so the coefficient is `(a)ₙ / (n! Γ(b + n))`.

## Main results

* `Complex.sum_regularizedHGFunCoeff_singleton_mul_neg_one_pow`: the coefficient identity
  `∑ₖ (−1)ᵏ 𝐌ₖ(b − a, b) / (n − k)! = 𝐌ₙ(a, b)` for the coefficients `𝐌ₙ` of the series.
* `Complex.regularizedHGFun_singleton_eq_exp_mul`: DLMF 13.2.39.

## References

* NIST Digital Library of Mathematical Functions, 13.2.39, <https://dlmf.nist.gov/13.2.E39>.
-/

public section

noncomputable section

open scoped Nat

namespace Complex

/-- The coefficients of `𝐌(b − a, b, −z)`, convolved with those of `e^z`, are the coefficients of
`𝐌(a, b, z)`: `∑ₖ (−1)ᵏ (b − a)ₖ / (k! (n − k)! Γ(b + k)) = (a)ₙ / (n! Γ(b + n))`, for every pair
of complex parameters, including the poles of `Γ`. -/
theorem sum_regularizedHGFunCoeff_singleton_mul_neg_one_pow (a b : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff {b - a} {b} k * (-1) ^ k * ((n - k)! : ℂ)⁻¹ =
    regularizedHGFunCoeff {a} {b} n := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff {b - a} {b} k * (-1) ^ k * ((n - k)! : ℂ)⁻¹ =
        (-1) ^ k * n.choose k * (ascPochhammer ℂ k).eval (b - a) *
          (ascPochhammer ℂ (n - k)).eval (b + k) / (n ! * Gamma (b + n)) := by
    intro k hk_mem
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk_mem)
    have hG : (Gamma (b + k))⁻¹ = (ascPochhammer ℂ (n - k)).eval (b + k) * (Gamma (b + n))⁻¹ := by
      have hbn : b + k + ((n - k : ℕ) : ℂ) = b + n := by rw [Nat.cast_sub hk]; ring
      rw [inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (b + k) (n - k), hbn]
    have hfac : (k ! : ℂ)⁻¹ * ((n - k)! : ℂ)⁻¹ = (n.choose k : ℂ) * (n ! : ℂ)⁻¹ := by
      simpa only [Nat.add_sub_of_le hk] using Nat.inv_factorial_mul_inv_factorial (K := ℂ) k (n - k)
    have hcoeff : regularizedHGFunCoeff {b - a} {b} k =
        (ascPochhammer ℂ k).eval (b - a) * (k ! : ℂ)⁻¹ * (Gamma (b + k))⁻¹ := by
      rw [regularizedHGFunCoeff_singleton, div_eq_mul_inv, mul_inv, mul_assoc]
    rw [hcoeff, hG, div_eq_mul_inv, mul_inv]
    linear_combination (ascPochhammer ℂ k).eval (b - a) * (-1) ^ k *
      (ascPochhammer ℂ (n - k)).eval (b + k) * (Gamma (b + n))⁻¹ * hfac
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div,
    TauCeti.sum_neg_one_pow_mul_choose_ascPochhammer, sub_sub_cancel,
    regularizedHGFunCoeff_singleton]

/-- **Kummer's transformation** (DLMF 13.2.39): `𝐌(a, b, z) = e^z 𝐌(b − a, b, −z)` for all
complex `a`, `b`, `z`. -/
theorem regularizedHGFun_singleton_eq_exp_mul (a b z : ℂ) :
    regularizedHGFun {a} {b} z = exp z * regularizedHGFun {b - a} {b} (-z) := by
  have hcard : ({b - a} : Multiset ℂ).card ≤ ({b} : Multiset ℂ).card := by simp
  have hM := hasSum_regularizedHGFun hcard (-z)
  have hE := NormedSpace.expSeries_div_hasSum_exp z
  have h := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_regularizedHGFun hcard (-z)) (NormedSpace.norm_expSeries_div_summable z)
  rw [hM.tsum_eq, hE.tsum_eq, ← exp_eq_exp_ℂ] at h
  have hsum (n : ℕ) : ∑ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff {b - a} {b} k * (-z) ^ k * (z ^ (n - k) / (n - k)!) =
        regularizedHGFunCoeff {a} {b} n * z ^ n := by
    rw [← sum_regularizedHGFunCoeff_singleton_mul_neg_one_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk_mem => ?_
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk_mem)
    rw [neg_pow, ← pow_mul_pow_sub z hk]
    ring
  simp only [hsum] at h
  rw [mul_comm]
  exact (hasSum_regularizedHGFun (by simp) z).unique h

end Complex
