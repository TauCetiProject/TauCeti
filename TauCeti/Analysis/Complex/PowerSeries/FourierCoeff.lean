/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.FourierCoeffOn

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
  (`DiffContOnCl.intervalIntegral_circleMap_zpow_smul_eq_zero`); on the unit circle, read as a
  function on `AddCircle (2 * π)`, its negative Fourier coefficients vanish
  (`DiffContOnCl.fourierCoeff_comp_toCircle_eq_zero`);
* on the unit circle, the angle integral of `w ^ m * F w` and the circle integral of `z ^ j * F z`
  are `2π` and `2π i` times Fourier coefficients of `θ ↦ F(e^{iθ})` on `[0, 2π]`
  (`TauCeti.intervalIntegral_circleMap_zpow_mul`, `TauCeti.circleIntegral_pow_mul`);
* the Fourier coefficients of the boundary defect `θ ↦ e^{ikθ} conj (T(e^{iθ})) - T(e^{iθ})` are
  `conj (a (k - n)) - a n` in terms of those `a` of `θ ↦ T(e^{iθ})`
  (`TauCeti.fourierCoeffOn_circleMap_zpow_mul_conj_sub`).
-/

public section

open Complex Metric
open scoped ComplexConjugate Real

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

local instance diffContOnClFourierCoeffTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- A function holomorphic on the open unit disc and continuous on its closure has vanishing
negative Fourier coefficients on the unit circle, read as a function on `AddCircle (2 * π)`. -/
theorem DiffContOnCl.fourierCoeff_comp_toCircle_eq_zero {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (ball 0 1)) {n : ℤ} (hn : n < 0) :
    fourierCoeff (fun x : AddCircle (2 * π) ↦ f (AddCircle.toCircle x)) n = 0 := by
  rw [fourierCoeff_eq_intervalIntegral (T := 2 * π) _ n 0, zero_add]
  have := hf.intervalIntegral_circleMap_zpow_smul_eq_zero one_pos (m := -n) (by omega)
  simp only [TauCeti.fourier_apply_eq_coe_toCircle_zpow, TauCeti.coe_toCircle_coe_eq_circleMap]
  simpa [zpow_neg] using this

namespace TauCeti

/-- The angle integral of `w ^ m * F w` over the unit circle is `2π` times the `-m`-th Fourier
coefficient of `θ ↦ F(e^{iθ})` on `[0, 2π]`. -/
theorem intervalIntegral_circleMap_zpow_mul (F : ℂ → ℂ) (m : ℤ) :
    ∫ θ in 0..2 * π, circleMap 0 1 θ ^ m * F (circleMap 0 1 θ) =
      2 * π * fourierCoeffOn Real.two_pi_pos (fun θ ↦ F (circleMap 0 1 θ)) (-m) := by
  rw [← fourierCoeff_comp_toCircle, fourierCoeff_eq_intervalIntegral (T := 2 * π) _ (-m) 0,
    zero_add]
  simp only [fourier_apply_eq_coe_toCircle_zpow, coe_toCircle_coe_eq_circleMap, neg_neg,
    smul_eq_mul, real_smul]
  push_cast
  field_simp

/-- The circle integral of `z ^ j * F z` over the unit circle is `2π i` times the `-(j + 1)`-th
Fourier coefficient of `θ ↦ F(e^{iθ})` on `[0, 2π]`. -/
theorem circleIntegral_pow_mul (F : ℂ → ℂ) (j : ℕ) :
    (∮ z in C(0, 1), z ^ j * F z) =
      I * (2 * π * fourierCoeffOn Real.two_pi_pos (fun θ ↦ F (circleMap 0 1 θ))
        (-((j : ℤ) + 1))) := by
  have h := circleIntegral_sub_zpow_sub_one_smul F 0 one_ne_zero ((j : ℤ) + 1)
  simp only [sub_zero, add_sub_cancel_right, zpow_natCast, smul_eq_mul] at h
  rw [h, intervalIntegral_circleMap_zpow_mul]

/-- The Fourier coefficients of the boundary defect `θ ↦ e^{ikθ} conj (T(e^{iθ})) - T(e^{iθ})` of a
continuous function `T` are `conj (a (k - n)) - a n`, where `a` are the Fourier coefficients of
`θ ↦ T(e^{iθ})` on `[0, 2π]`. -/
theorem fourierCoeffOn_circleMap_zpow_mul_conj_sub {T : ℂ → ℂ} (hT : Continuous T) (k n : ℤ) :
    fourierCoeffOn Real.two_pi_pos
      (fun θ ↦ circleMap 0 1 θ ^ k * conj (T (circleMap 0 1 θ)) - T (circleMap 0 1 θ)) n =
      conj (fourierCoeffOn Real.two_pi_pos (fun θ ↦ T (circleMap 0 1 θ)) (k - n)) -
        fourierCoeffOn Real.two_pi_pos (fun θ ↦ T (circleMap 0 1 θ)) n := by
  have hTc : Continuous fun x : AddCircle (2 * π) ↦ T (AddCircle.toCircle x) :=
    continuous_comp_toCircle (hT.comp (continuous_circleMap 0 1))
  have hTc' : Continuous fun x : AddCircle (2 * π) ↦
      fourier k x * conj (T (AddCircle.toCircle x)) :=
    (map_continuous (fourier k)).mul (continuous_conj.comp hTc)
  have hi {g : AddCircle (2 * π) → ℂ} (hg : Continuous g) :
      MeasureTheory.Integrable g AddCircle.haarAddCircle :=
    hg.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hfun : (fun x : AddCircle (2 * π) ↦ (AddCircle.toCircle x : ℂ) ^ k *
      conj (T (AddCircle.toCircle x)) - T (AddCircle.toCircle x)) =
      fun x ↦ fourier k x * conj (T (AddCircle.toCircle x)) - T (AddCircle.toCircle x) :=
    funext fun x ↦ by rw [fourier_apply_eq_coe_toCircle_zpow]
  rw [← fourierCoeff_comp_toCircle (fun w ↦ w ^ k * conj (T w) - T w), hfun,
    fourierCoeff_sub (hi hTc') (hi hTc), fourierCoeff_fourier_mul_conj, fourierCoeff_comp_toCircle,
    fourierCoeff_comp_toCircle]

end TauCeti
