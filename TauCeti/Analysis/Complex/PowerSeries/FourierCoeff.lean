/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Cauchy coefficients as Fourier coefficients of boundary values

For a function `f : ℂ → E` and a circle `C(c, R)` with `R ≠ 0`, write
`bₘ = ∫ θ in 0..2π, (R e^{iθ}) ^ m • f (c + R e^{iθ})`. In the standard convention
`f̂(n) = (2π)⁻¹ ∫ e^{-inθ} f`, `bₘ` is `2π Rᵐ` times the `(-m)`-th Fourier coefficient of
`θ ↦ f (c + R e^{iθ})`. This file records:

* the circle integral of `(z - c) ^ (m - 1) • f z` is `I • bₘ`
  (`TauCeti.circleIntegral_sub_zpow_sub_one_smul`);
* the coefficients of the Cauchy power series `cauchyPowerSeries f c R` are
  `(2π)⁻¹ • b₋ₙ` (`TauCeti.coeff_cauchyPowerSeries`);
* for `f` holomorphic on the open disc and continuous on its closure, the integrals `bₘ`
  with `m > 0`, that is the negative-degree Fourier coefficients, vanish by Cauchy's theorem
  (`DiffContOnCl.intervalIntegral_circleMap_zpow_smul_eq_zero`).
-/

public section

open Complex Metric
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TauCeti

/-- A circle integral against `(z - c) ^ (m - 1)`, written in the angle variable. -/
theorem circleIntegral_sub_zpow_sub_one_smul (f : ℂ → E) (c : ℂ) {R : ℝ} (hR : R ≠ 0) (m : ℤ) :
    (∮ z in C(c, R), (z - c) ^ (m - 1) • f z) =
      I • ∫ θ in 0..2 * π, circleMap 0 R θ ^ m • f (circleMap c R θ) := by
  rw [circleIntegral, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hz : circleMap 0 R θ ≠ 0 := circleMap_ne_center hR
  simp only [deriv_circleMap, circleMap_sub_center, smul_smul, zpow_sub_one₀ hz]
  congr 1
  field_simp

/-- The coefficients of the Cauchy power series of `f` on the circle `C(c, R)` are the Fourier
coefficients of `θ ↦ f (c + R e^{iθ})`, weighted by `R⁻ⁿ`. -/
theorem coeff_cauchyPowerSeries (f : ℂ → E) (c : ℂ) {R : ℝ} (hR : R ≠ 0) (n : ℕ) :
    (cauchyPowerSeries f c R).coeff n =
      (2 * π : ℂ)⁻¹ • ∫ θ in 0..2 * π, circleMap 0 R θ ^ (-(n : ℤ)) • f (circleMap c R θ) := by
  have h := (cauchyPowerSeries f c R).apply_eq_pow_smul_coeff (n := n) (z := 1)
  rw [one_pow, one_smul] at h
  have hint : (∮ z in C(c, R), (1 / (z - c)) ^ n • (z - c)⁻¹ • f z) =
      ∮ z in C(c, R), (z - c) ^ (-(n : ℤ) - 1) • f z := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hz0 : circleMap c R θ - c ≠ 0 := sub_ne_zero.mpr (circleMap_ne_center hR)
    simp only [smul_smul, zpow_sub_one₀ hz0, zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [← h, cauchyPowerSeries_apply, hint, circleIntegral_sub_zpow_sub_one_smul f c hR, smul_smul]
  congr 1
  field_simp

end TauCeti

/-- For a function holomorphic on an open disc and continuous on its closure, the integrals
`∫ θ in 0..2π, (R e^{iθ}) ^ m • f (c + R e^{iθ})` with `m > 0` vanish, by Cauchy's theorem: these
are the negative-degree Fourier coefficients of the boundary values. -/
theorem DiffContOnCl.intervalIntegral_circleMap_zpow_smul_eq_zero {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) {m : ℤ} (hm : 0 < m) :
    ∫ θ in 0..2 * π, circleMap 0 R θ ^ m • f (circleMap c R θ) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := ⟨(m - 1).toNat, by omega⟩
  have h : (∮ z in C(c, R), (z - c) ^ n • f z) = 0 :=
    (((differentiable_id.sub_const c).pow n).diffContOnCl.smul hf).circleIntegral_eq_zero hR.le
  have h' := TauCeti.circleIntegral_sub_zpow_sub_one_smul f c hR.ne' (n + 1)
  simp only [add_sub_cancel_right, zpow_natCast] at h'
  rw [h] at h'
  exact (smul_eq_zero.mp h'.symm).resolve_left I_ne_zero
