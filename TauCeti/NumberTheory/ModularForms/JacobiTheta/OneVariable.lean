/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Transformation identities and estimates for the one-variable Jacobi theta function

Two identities and two estimates for Mathlib's `jacobiTheta`, `θ(τ) = ∑_n e^{πi n² τ}`,
complementing the transformation laws in
`Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable`.

## Main results

* `TauCeti.jacobiTheta_sub_natCast_div_two`: splitting `n` by parity,
  `θ(τ - N/2) = e^{-πiN/2} θ(τ) + (1 - e^{-πiN/2}) θ(4τ)` for every natural number `N`.
* `TauCeti.jacobiTheta_I_mul`: the functional equation on the imaginary axis,
  `θ(iy) = θ(i/y) / √y` for `y > 0`.
* `TauCeti.norm_jacobiTheta₂_sub_one_le`: for real `z`, `‖θ₂(z, τ) - 1‖ ≤ ‖θ(i im τ) - 1‖`.
* `TauCeti.tendsto_jacobiTheta_comap_im_atTop`: `θ(τ) → 1` as `im τ → ∞`.
-/

public section

open Complex Filter Topology
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

/-- For real `z`, the two-variable theta function `θ₂(z, τ)` is at least as close to `1` as
`θ(i im τ)`: its terms have the absolute values `e^{-π n² im τ}` of the terms of `θ(i im τ)`. -/
theorem norm_jacobiTheta₂_sub_one_le {z τ : ℂ} (hz : z.im = 0) (hτ : 0 < τ.im) :
    ‖jacobiTheta₂ z τ - 1‖ ≤ ‖jacobiTheta (I * τ.im) - 1‖ := by
  -- The common absolute values of the terms, kept opaque so that `simp` does not unfold them.
  obtain ⟨b, hb⟩ : ∃ b : ℤ → ℝ, b = fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * τ.im) := ⟨_, rfl⟩
  have hterm (n : ℤ) : jacobiTheta₂_term n 0 (I * τ.im) = b n := by
    rw [hb, jacobiTheta₂_term, ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hnorm (n : ℤ) : ‖jacobiTheta₂_term n z τ‖ = b n := by
    rw [norm_jacobiTheta₂_term, hz, hb]
    ring_nf
  have hsa := (summable_jacobiTheta₂_term_iff z τ).2 hτ
  have hsb : Summable b := by simpa only [hnorm] using hsa.norm
  have hb0 (n : ℤ) : 0 ≤ if n = 0 then 0 else b n := by
    split_ifs
    · exact le_rfl
    · rw [hb]
      exact (Real.exp_pos _).le
  have ha : jacobiTheta₂ z τ - 1 = ∑' n, if n = 0 then 0 else jacobiTheta₂_term n z τ := by
    rw [jacobiTheta₂, hsa.tsum_eq_add_tsum_ite 0, jacobiTheta₂_term]
    simp
  have hb' : jacobiTheta (I * τ.im) - 1 = ((∑' n, if n = 0 then 0 else b n : ℝ) : ℂ) := by
    rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂]
    simp_rw [hterm]
    rw [← ofReal_tsum, hsb.tsum_eq_add_tsum_ite 0, ofReal_add]
    simp [hb]
  have hupd (n : ℤ) :
      ‖if n = 0 then 0 else jacobiTheta₂_term n z τ‖ = if n = 0 then 0 else b n := by
    split_ifs
    · exact norm_zero
    · exact hnorm n
  rw [ha, hb', norm_real, Real.norm_of_nonneg (tsum_nonneg hb0)]
  refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hupd)
  simp only [hupd]
  exact (hasSum_ite_sub_hasSum hsb.hasSum 0).summable

/-- The theta function tends to `1` as `im τ → ∞`. -/
theorem tendsto_jacobiTheta_comap_im_atTop :
    Tendsto jacobiTheta (comap im atTop) (𝓝 1) := by
  have h : Tendsto (fun τ : ℂ ↦ rexp (-π * τ.im)) (comap im atTop) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_comap.const_mul_atTop_of_neg (neg_neg_of_pos Real.pi_pos))
  simpa using (isBigO_at_im_infty_jacobiTheta_sub_one.trans_tendsto h).add_const 1

end TauCeti
