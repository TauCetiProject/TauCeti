/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The complex Gamma function on vertical lines

On a vertical line `Re s = σ` the complex Gamma function decays faster than every power of
`|Im s|`. This file records the elementary form of that decay which suffices for contour
arguments with integrands of polynomial growth, and the Mellin inversion formula for `Γ`.

For `Re s > 0` the Euler integral gives `‖Γ(s)‖ ≤ Γ(Re s)`. Applying this to `s + n` and using
`Γ(s + n) = s (s + 1) ⋯ (s + n - 1) Γ(s)` gives, for every `s` with `Re s + n > 0`,

`‖Γ(s)‖ ‖s‖ ‖s + 1‖ ⋯ ‖s + n - 1‖ ≤ Γ(Re s + n)`,

which also holds at the poles of `Γ` in that half-plane, where a factor `s + k` vanishes. Since
`‖s + k‖ ≥ |Im s|`, this gives `Γ(σ + i t) = O(|t|⁻ⁿ)` for every `n` without any Stirling
asymptotics; on a vertical line avoiding the poles it gives the explicit bounds
`‖Γ(σ + i t)‖ ≤ C (1 + t²)⁻ᵐ` for every `m`, so `Γ` is integrable on every such line.

Since `Γ` is the Mellin transform of `t ↦ e⁻ᵗ`, Mellin inversion recovers the exponential from
`Γ` on any vertical line `Re s = σ > 0`:

`e⁻ˣ = (1 / 2π) ∫ Γ(σ + i t) x^{-(σ + i t)} dt` for `x > 0`.

This is the smoothing kernel that turns a Dirichlet series into an exponentially weighted sum of
its coefficients.

## Main results

* `Complex.norm_Gamma_le_Gamma_re`: `‖Γ(s)‖ ≤ Γ(Re s)` for `Re s > 0`.
* `Complex.norm_Gamma_mul_prod_norm_le`: `‖Γ(s)‖ ∏_{k < n} ‖s + k‖ ≤ Γ(Re s + n)` whenever
  `Re s + n > 0`.
* `Complex.exists_norm_Gamma_le_mul_inv_one_add_sq_pow`: `‖Γ(σ + i t)‖ ≤ C (1 + t²)⁻ᵐ` for every
  `m` on every vertical line `Re s = σ` with `σ` not a nonpositive integer.
* `Complex.verticalIntegrable_Gamma`: `Γ` is integrable on every vertical line `Re s = σ` with
  `σ` not a nonpositive integer.
* `Complex.mellinInv_Gamma`: Mellin inversion of `Γ` on `Re s = σ > 0` gives `e⁻ˣ`.
* `Complex.integral_cpow_neg_mul_Gamma`: the same formula as the unnormalised vertical integral
  `∫ y^{-(σ + i t)} Γ(σ + i t) dt = 2π e⁻ʸ`.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §4.42 (the Euler integral) and §9.5 (Mellin
  inversion).
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055
  (the smoothing kernel `Γ(s) xˢ` in the proof of Siegel's theorem).
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp

namespace Complex

/-- On the right half-plane the complex Gamma function is bounded by the real Gamma function of
the real part: `‖Γ(s)‖ ≤ Γ(Re s)`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, Real.Gamma_eq_integral hs, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq (setIntegral_congr_fun measurableSet_Ioi
    fun x (hx : 0 < x) ↦ ?_)
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]

/-- The polynomial decay of the Gamma function on vertical lines:
`‖Γ(s)‖ ‖s‖ ‖s + 1‖ ⋯ ‖s + n - 1‖ ≤ Γ(Re s + n)` whenever `Re s + n > 0`. This holds also at the
poles of `Γ` in the half-plane `Re s > -n`, where one of the factors `s + k` vanishes. -/
theorem norm_Gamma_mul_prod_norm_le {s : ℂ} {n : ℕ} (hs : 0 < s.re + n) :
    ‖Gamma s‖ * ∏ k ∈ Finset.range n, ‖s + k‖ ≤ Real.Gamma (s.re + n) := by
  induction n generalizing s with
  | zero => simpa using norm_Gamma_le_Gamma_re (by simpa using hs)
  | succ n ih =>
    rcases eq_or_ne s 0 with rfl | hs0
    · simp only [Finset.prod_range_succ', zero_add, Nat.cast_zero, norm_zero, mul_zero]
      exact (Real.Gamma_pos_of_pos (by simpa using hs)).le
    have h := ih (s := s + 1) (by push_cast at hs ⊢; simp only [add_re, one_re]; linarith)
    have hΓ : ‖Gamma (s + 1)‖ = ‖s‖ * ‖Gamma s‖ := by rw [Gamma_add_one s hs0, norm_mul]
    have hprod : ∏ k ∈ Finset.range n, ‖s + ((k + 1 : ℕ) : ℂ)‖ =
        ∏ k ∈ Finset.range n, ‖s + 1 + k‖ :=
      Finset.prod_congr rfl fun k _ ↦ by push_cast; ring_nf
    rw [Finset.prod_range_succ', hprod,
      show s.re + ((n + 1 : ℕ) : ℝ) = (s + 1).re + n by simp; ring]
    calc _ = ‖Gamma (s + 1)‖ * ∏ k ∈ Finset.range n, ‖s + 1 + k‖ := by rw [hΓ]; simp; ring
      _ ≤ _ := h

/-- On a vertical line `Re s = σ` avoiding the poles of the Gamma function, `Γ(σ + i t)` decays
faster than every power of `|t|`: for every `m`, `‖Γ(σ + i t)‖` is bounded by a constant multiple
of `(1 + t²)⁻ᵐ`. -/
theorem exists_norm_Gamma_le_mul_inv_one_add_sq_pow {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Gamma (σ + t * I)‖ ≤ C * ((1 + t ^ 2) ^ m)⁻¹ := by
  obtain ⟨n, hn2, hn⟩ : ∃ n : ℕ, 2 * m ≤ n ∧ 0 < σ + n :=
    ⟨⌈-σ⌉₊ + 2 * m + 1, by omega, by push_cast; linarith [Nat.le_ceil (-σ)]⟩
  set c : ℝ := ∏ k ∈ Finset.range n, min ((σ + k) ^ 2) 1
  have hc : 0 < c := Finset.prod_pos fun k _ ↦ lt_min (by
    have : σ + k ≠ 0 := fun h ↦ hσ k (by linarith)
    positivity) one_pos
  refine ⟨Real.Gamma (σ + n) / √c, fun t ↦ ?_⟩
  set s : ℂ := σ + t * I
  have hre : s.re = σ := by simp [s]
  have hT : 0 < 1 + t ^ 2 := by positivity
  -- each factor satisfies `‖s + k‖² ≥ min ((σ + k)², 1) (1 + t²)`
  have hfac (k : ℕ) : min ((σ + k) ^ 2) 1 * (1 + t ^ 2) ≤ ‖s + k‖ ^ 2 := by
    have : ‖s + k‖ ^ 2 = (σ + k) ^ 2 + t ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp [s]; ring
    rw [this]
    nlinarith [min_le_left ((σ + k) ^ 2) 1, min_le_right ((σ + k) ^ 2) 1, sq_nonneg t,
      le_min (sq_nonneg (σ + k)) zero_le_one]
  have hprod : c * ((1 + t ^ 2) ^ m) ^ 2 ≤ (∏ k ∈ Finset.range n, ‖s + k‖) ^ 2 := by
    calc c * ((1 + t ^ 2) ^ m) ^ 2 ≤ c * (1 + t ^ 2) ^ n := by
          rw [← pow_mul, mul_comm m]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by nlinarith) hn2) hc.le
      _ = ∏ k ∈ Finset.range n, min ((σ + k) ^ 2) 1 * (1 + t ^ 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ ≤ ∏ k ∈ Finset.range n, ‖s + k‖ ^ 2 :=
          Finset.prod_le_prod₀ (fun k _ ↦ mul_nonneg (le_min (sq_nonneg _) zero_le_one) hT.le)
            fun k _ ↦ hfac k
      _ = _ := Finset.prod_pow _ _ _
  have hbound := norm_Gamma_mul_prod_norm_le (s := s) (n := n) (by rw [hre]; exact hn)
  rw [hre] at hbound
  have hsq : (√c * (1 + t ^ 2) ^ m) ^ 2 ≤ (∏ k ∈ Finset.range n, ‖s + k‖) ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hc.le]
  have hP : √c * (1 + t ^ 2) ^ m ≤ ∏ k ∈ Finset.range n, ‖s + k‖ :=
    le_of_pow_le_pow_left₀ two_ne_zero (Finset.prod_nonneg fun k _ ↦ norm_nonneg _) hsq
  rw [show Real.Gamma (σ + n) / √c * ((1 + t ^ 2) ^ m)⁻¹ =
      Real.Gamma (σ + n) / (√c * (1 + t ^ 2) ^ m) by field_simp, le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left hP (norm_nonneg _)).trans hbound

/-- The Gamma function is integrable on every vertical line `Re s = σ` which avoids its poles,
that is, for `σ` not a nonpositive integer. -/
theorem verticalIntegrable_Gamma {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    VerticalIntegrable Gamma σ := by
  obtain ⟨C, hC⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hσ 1
  refine (integrable_inv_one_add_sq.const_mul C).mono' ?_
    (Eventually.of_forall fun t ↦ by simpa using hC t)
  refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun t ↦ ?_)
  refine (differentiableAt_Gamma _ fun m h ↦ hσ m ?_).continuousAt.comp (by fun_prop)
  simpa using congrArg re h

/-- Mellin inversion for the Gamma function: on every vertical line `Re s = σ > 0`,
`(1 / 2π) ∫ x^{-(σ + i t)} Γ(σ + i t) dt = e⁻ˣ` for `x > 0`. -/
theorem mellinInv_Gamma {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ Gamma x = Real.exp (-x) := by
  have hline : ∀ t : ℝ, Gamma (σ + t * I) = mellin (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) (σ + t * I) :=
    fun t ↦ by rw [← GammaIntegral_eq_mellin, Gamma_eq_integral (by simpa using hσ)]
  have hint : VerticalIntegrable (mellin fun u : ℝ ↦ (Real.exp (-u) : ℂ)) σ := by
    refine (verticalIntegrable_Gamma fun n h ↦ ?_).congr (Eventually.of_forall hline)
    linarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have hconv : MellinConvergent (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) σ := by
    refine (GammaIntegral_convergent (s := σ) (by simpa using hσ)).congr_fun (fun u _ ↦ ?_)
      measurableSet_Ioi
    simp [smul_eq_mul, mul_comm]
  have h := mellinInv_mellin_eq σ _ hx hconv hint (by fun_prop)
  rw [← h, mellinInv, mellinInv]
  simp_rw [hline]

/-- Mellin inversion for the Gamma function as an integral: on every vertical line
`Re s = σ > 0`, `∫ y^{-(σ + i t)} Γ(σ + i t) dt = 2π e⁻ʸ` for `y > 0`. -/
theorem integral_cpow_neg_mul_Gamma {σ : ℝ} (hσ : 0 < σ) {y : ℝ} (hy : 0 < y) :
    ∫ t : ℝ, (y : ℂ) ^ (-(σ + t * I)) * Gamma (σ + t * I) = 2 * π * Real.exp (-y) := by
  have h := mellinInv_Gamma hσ hy
  rw [mellinInv, real_smul] at h
  simp only [smul_eq_mul] at h
  rw [← h, ← mul_assoc,
    show (2 * π : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]

end Complex
