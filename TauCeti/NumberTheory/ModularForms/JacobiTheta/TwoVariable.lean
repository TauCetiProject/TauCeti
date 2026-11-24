/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier coefficients of the two-variable Jacobi theta function

For a nonzero integer `k`, the function `x ↦ θ(kx + w, τ)` built from Mathlib's `jacobiTheta₂` is
`1`-periodic, and its Fourier series is its theta series `∑_n e^{2πinw + πin²τ} e^{2πiknx}`.

## Main results

* `TauCeti.integral_cexp_mul_jacobiTheta₂_mul_add`: the Fourier coefficients of `x ↦ θ(kx + w, τ)`
  for a nonzero integer `k`, by termwise integration of the theta series.
-/

public section

open Complex MeasureTheory
open scoped Real Interval

namespace TauCeti

/-- **Fourier coefficients of a rescaled theta function.** For a nonzero integer `k`, the function
`x ↦ θ(kx + w, τ)` is `1`-periodic with Fourier series `∑_n e^{2πinw + πin²τ} e^{2πiknx}`, so its
Fourier coefficient at frequency `-j` is the term of index `-j / k` when `k ∣ j`, and `0`
otherwise. -/
theorem integral_cexp_mul_jacobiTheta₂_mul_add {k : ℤ} (hk : k ≠ 0) (j : ℤ) (w : ℂ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ∫ x in (0 : ℝ)..1, cexp (2 * π * I * j * x) * jacobiTheta₂ (k * x + w) τ =
      if k ∣ j then jacobiTheta₂_term (-(j / k)) w τ else 0 := by
  -- Integrate the theta series termwise: each term is a multiple of `e^{2πi(j + kn)x}`.
  let f : ℤ → ContinuousMap ℝ ℂ := fun n ↦
    ⟨fun x ↦ jacobiTheta₂_term n w τ * cexp (2 * π * I * (j + k * n) * x), by fun_prop⟩
  have hterm (x : ℝ) :
      cexp (2 * π * I * j * x) * jacobiTheta₂ (k * x + w) τ = ∑' n, f n x := by
    rw [jacobiTheta₂, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    simp only [f, ContinuousMap.coe_mk, jacobiTheta₂_term, ← exp_add]
    ring_nf
  have hnorm (n : ℤ) :
      ‖(f n).restrict (⟨[[(0 : ℝ), 1]], isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
        ‖jacobiTheta₂_term n w τ‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ ?_
    simp only [ContinuousMap.restrict_apply, f, ContinuousMap.coe_mk, norm_mul]
    rw [show 2 * π * I * (j + k * n) * (x : ℂ) = ((2 * π * (j + k * n) * x : ℝ) : ℂ) * I by
      push_cast; ring, norm_exp_ofReal_mul_I, mul_one]
  have hsum := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hnorm
    (summable_norm_iff.2 ((summable_jacobiTheta₂_term_iff w τ).2 hτ))
  have hint (n : ℤ) : ∫ x in (0 : ℝ)..1, f n x =
      if j + k * n = 0 then jacobiTheta₂_term n w τ else 0 := by
    simp only [f, ContinuousMap.coe_mk]
    rw [intervalIntegral.integral_const_mul]
    split_ifs with hn
    · have : (j : ℂ) + k * n = 0 := by exact_mod_cast hn
      simp [this]
    · have hn' : (j : ℂ) + k * n ≠ 0 := by exact_mod_cast hn
      rw [integral_exp_mul_complex (by simp [hn', Real.pi_ne_zero, I_ne_zero]),
        show 2 * π * I * (j + k * n) * ((1 : ℝ) : ℂ) = ((j + k * n : ℤ) : ℂ) * (2 * π * I) by
          push_cast; ring, exp_int_mul_two_pi_mul_I]
      simp
  rw [intervalIntegral.integral_congr fun x _ ↦ hterm x,
    ← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum, tsum_congr hint]
  split_ifs with hkj
  · obtain ⟨q, rfl⟩ := hkj
    rw [Int.mul_ediv_cancel_left q hk,
      tsum_eq_single (-q) fun n hn ↦ ite_eq_right_iff.2 fun h ↦ (hn ?_).elim]
    · simp
    · have : k * (q + n) = 0 := by rw [mul_add]; exact h
      rcases mul_eq_zero.1 this with h | h
      · exact (hk h).elim
      · omega
  · exact (tsum_congr fun n ↦ ite_eq_right_iff.2 fun h ↦
      (hkj ⟨-n, by linear_combination h⟩).elim).trans tsum_zero

end TauCeti
