/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.CauchyIntegral

import TauCeti.Analysis.Fourier.FourierCoeffOn

/-!
# Decay of Fourier transforms and Fourier coefficients of smooth functions

A smooth compactly supported function is a Schwartz function, so its Fourier transform is again a
Schwartz function and therefore decays faster than every negative power of `‖v‖`. This file records
that decay in the elementary form `‖v‖ ^ k * ‖𝓕 f v‖ ≤ C`, which is the shape a Fourier transform
is used in when it weights a comparison test. Without smoothness or compact support, integrating by
parts `N` times gives the explicit bound `(2π ‖w‖) ^ N ‖𝓕 f w‖ ≤ ∫ ‖D^N f‖` for a `C^N` function
whose derivatives up to order `N` are integrable. The file also records the angular-frequency form
`∫ exp(-i ⟪v, ξ⟫) f v dv = 𝓕 f ((2π)⁻¹ ξ)` of the Fourier transform, whose integrand is
integrable whenever `f` is.

The periodic analogue concerns Fourier coefficients on `AddCircle T`. Integrating by parts over a
period, with no boundary term by periodicity, multiplies the `n`-th Fourier coefficient by
`2πin / T` for each derivative. A `C^k` function on the circle therefore has Fourier coefficients
of size `O(|n| ^ (-k))`. This is what makes smooth functions act boundedly, by multiplication, on
the Fourier-coefficient Sobolev spaces of the circle. A function extending holomorphically to a
strip around the real axis has exponentially decaying Fourier coefficients, by Cauchy's theorem.

## Main declarations

* `TauCeti.exists_norm_pow_mul_norm_fourier_le`: for every exponent `k`, the Fourier transform of a
  smooth compactly supported function on a finite-dimensional real inner product space satisfies
  `‖v‖ ^ k * ‖𝓕 f v‖ ≤ C` for some `C > 0`.
* `TauCeti.exists_one_add_norm_pow_mul_norm_fourier_le`: the same decay with the weight
  `(1 + ‖v‖) ^ k`.
* `TauCeti.pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv`: if `f` is `C^N` and its
  derivatives up to order `N` are integrable, then `(2π ‖w‖) ^ N ‖𝓕 f w‖ ≤ ∫ ‖D^N f‖`.
* `TauCeti.fourier_fderiv_apply`: the Fourier transform of the directional derivative `∂_v f` of a
  `C¹` compactly supported function is `2πi ⟪w, v⟫ 𝓕 f w`.
* `TauCeti.integral_exp_smul_eq_fourier`: the integral `∫ exp(-i ⟪v, ξ⟫) f v dv` in angular
  frequency is the Fourier transform `𝓕 f ((2π)⁻¹ ξ)`.
* `TauCeti.integrable_exp_neg_inner_smul`: multiplying an integrable function by the phase
  `exp(-i ⟪v, ξ⟫)` keeps it integrable.
* `TauCeti.exists_abs_pow_mul_norm_fourierCoeff_le`: if `f : AddCircle T → ℂ` is `C^k` as a
  periodic function on `ℝ`, then `|n| ^ k * ‖fourierCoeff f n‖ ≤ C` for some `C`.
* `TauCeti.periodic_cexp_two_pi_mul_I_mul_div`: the Fourier monomial `z ↦ e^{2πinz/T}` on `ℂ` is
  `T`-periodic.
* `TauCeti.integral_eq_integral_add_mul_I_of_differentiableOn_strip`: the integral over a period of
  a periodic function holomorphic on a strip `|Im z| ≤ |y|` is unchanged by shifting the line of
  integration to `Im z = y`.
* `TauCeti.norm_fourierCoeff_le_of_differentiableOn_strip`: if `f : AddCircle T → ℂ` extends to a
  periodic function holomorphic and bounded by `M` on the strip `|Im z| ≤ δ`, then
  `‖fourierCoeff f n‖ ≤ M e^{-2π |n| δ / T}`.
-/

public section

open scoped ContDiff FourierTransform

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of a smooth compactly supported function decays faster than every power
of `‖v‖⁻¹`, because it is a Schwartz function. -/
theorem exists_norm_pow_mul_norm_fourier_le (hf : ContDiff ℝ ∞ f) (hsupp : HasCompactSupport f)
    (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ v : V, ‖v‖ ^ k * ‖𝓕 f v‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := (𝓕 (hsupp.toSchwartzMap hf) : SchwartzMap V E).decay k 0
  refine ⟨C, hC0, fun v ↦ ?_⟩
  have hcoe0 : ⇑(hsupp.toSchwartzMap hf) = f := by
    ext u
    simp
  have h := hC v
  rwa [norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe, hcoe0] at h

/-- The Fourier transform of a smooth compactly supported function decays faster than every power
of `(1 + ‖v‖)⁻¹`, because it is a Schwartz function. -/
theorem exists_one_add_norm_pow_mul_norm_fourier_le (hf : ContDiff ℝ ∞ f)
    (hsupp : HasCompactSupport f) (k : ℕ) : ∃ C : ℝ, ∀ v : V, (1 + ‖v‖) ^ k * ‖𝓕 f v‖ ≤ C := by
  have hcoe : ⇑(hsupp.toSchwartzMap hf) = f := funext (hsupp.toSchwartzMap_toFun hf)
  let g : SchwartzMap V E := 𝓕 (hsupp.toSchwartzMap hf)
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) g,
    fun v ↦ ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl g v
  rwa [norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe, hcoe] at h

open MeasureTheory Real in
/-- **Integration by parts.** If `f` is `C^N` and its derivatives of order at most `N` are
integrable, then `(2π ‖w‖) ^ N ‖𝓕 f w‖ ≤ ∫ ‖D^N f‖`. -/
theorem pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv {N : ℕ} (hf : ContDiff ℝ N f)
    (hf' : ∀ n ≤ N, Integrable (iteratedFDeriv ℝ n f)) (w : V) :
    (2 * π * ‖w‖) ^ N * ‖𝓕 f w‖ ≤ ∫ v, ‖iteratedFDeriv ℝ N f v‖ := by
  have key := congrFun (Real.fourier_iteratedFDeriv (N := N) hf
    (fun n hn ↦ hf' n (mod_cast hn)) le_rfl) w
  have hle : ‖𝓕 (iteratedFDeriv ℝ N f) w (fun _ ↦ w)‖ ≤
      (∫ v, ‖iteratedFDeriv ℝ N f v‖) * ‖w‖ ^ N := by
    refine ((𝓕 (iteratedFDeriv ℝ N f) w).le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact Real.norm_fourier_le_integral_norm _ _
  have heq : ‖𝓕 (iteratedFDeriv ℝ N f) w (fun _ ↦ w)‖ =
      (2 * π * ‖w‖) ^ N * ‖𝓕 f w‖ * ‖w‖ ^ N := by
    rw [key, VectorFourier.fourierPowSMulRight_apply]
    simp only [neg_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_smul,
      norm_pow, norm_neg, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos pi_pos, Complex.norm_I, mul_one]
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity)]
    ring
  rcases eq_or_ne (‖w‖ ^ N) 0 with h | h
  · obtain ⟨hw, hN⟩ := pow_eq_zero_iff'.mp h
    rw [hw, mul_zero, zero_pow hN, zero_mul]
    exact integral_nonneg fun _ ↦ norm_nonneg _
  · exact le_of_mul_le_mul_right (heq ▸ hle) (lt_of_le_of_ne (by positivity) (Ne.symm h))

open MeasureTheory Real in
open scoped RealInnerProductSpace in
/-- **The Fourier transform of a directional derivative.** For a `C¹` function `f` with compact
support, the Fourier transform of `x ↦ ∂_v f(x)` at `w` is `2πi ⟪w, v⟫ 𝓕 f w`. -/
theorem fourier_fderiv_apply (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (v w : V) :
    𝓕 (fun x ↦ fderiv ℝ f x v) w = ((2 * π * Complex.I * ⟪w, v⟫ : ℂ)) • 𝓕 f w := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hf' : Integrable (fderiv ℝ f) :=
    (hf.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hfc.fderiv (𝕜 := ℝ))
  rw [← Real.fourier_continuousLinearMap_apply hf', Real.fourier_fderiv hfi
    (hf.differentiable one_ne_zero) hf']
  simp only [VectorFourier.fourierSMulRight_apply, neg_apply, smul_neg, neg_smul, neg_neg]
  rw [← Complex.coe_smul, smul_smul, innerSL_apply_apply]

open Real in
open scoped RealInnerProductSpace in
/-- The Fourier transform in angular frequency: `∫ exp(-i ⟪v, ξ⟫) f v dv = 𝓕 f ((2π)⁻¹ ξ)`. -/
theorem integral_exp_smul_eq_fourier (f : V → E) (ξ : V) :
    ∫ v, Complex.exp (-(⟪v, ξ⟫ * Complex.I)) • f v = 𝓕 f ((2 * π)⁻¹ • ξ) := by
  rw [Real.fourier_eq']
  congr 1 with v
  rw [inner_smul_right]
  congr 2
  push_cast
  field_simp

open MeasureTheory in
open scoped RealInnerProductSpace in
/-- Multiplying an integrable function by the phase `exp(-i ⟪v, ξ⟫)` keeps it integrable. -/
theorem integrable_exp_neg_inner_smul (hf : Integrable f) (ξ : V) :
    Integrable fun v ↦ Complex.exp (-(⟪v, ξ⟫ * Complex.I)) • f v :=
  hf.norm.mono' ((by fun_prop : Continuous fun v : V ↦
    Complex.exp (-(⟪v, ξ⟫ * Complex.I))).aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (ae_of_all _ fun v ↦ by simp [norm_smul, Complex.norm_exp])

section Circle

open Complex
open scoped Real Interval

variable {T : ℝ} [hT : Fact (0 < T)]

/-- **Decay of the Fourier coefficients of a `C^k` function on the circle.** If a function on
`AddCircle T` is `C^k` as a periodic function on `ℝ`, then `|n| ^ k * ‖fourierCoeff f n‖` is
bounded. -/
theorem exists_abs_pow_mul_norm_fourierCoeff_le {f : AddCircle T → ℂ} {k : ℕ}
    (hf : ContDiff ℝ k fun x : ℝ ↦ f x) :
    ∃ C, ∀ n : ℤ, |(n : ℝ)| ^ k * ‖fourierCoeff f n‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 0 + T)).exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv k le_rfl).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, by linarith [hT.out]⟩)
  refine ⟨(T / (2 * π)) ^ k * M, fun n ↦ ?_⟩
  have hbound := norm_fourierCoeffOn_le (lt_add_of_pos_right 0 hT.out)
    (fun x hx ↦ hM x (Set.Ioc_subset_Icc_self hx)) n
  rw [fourierCoeff_eq_fourierCoeffOn 0]
  rcases eq_or_ne n 0 with rfl | hn
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hbound
    · simp only [Int.cast_zero, abs_zero, zero_pow hk.ne', zero_mul]
      have := hT.out
      positivity
  · rw [fourierCoeffOn_iteratedDeriv hf (fun x ↦ by simp) 0 n le_rfl, norm_mul,
      norm_pow] at hbound
    have hnorm : ‖(2 * π * I * n / T : ℂ)‖ = 2 * π * |(n : ℝ)| / T := by
      simp [abs_of_pos hT.out]
    rw [hnorm, div_pow, mul_pow] at hbound
    have hT0 : 0 < T ^ k := pow_pos hT.out k
    have hπ : 0 < (2 * π) ^ k := pow_pos (by positivity) k
    rw [div_pow]
    calc |(n : ℝ)| ^ k * _ = T ^ k / (2 * π) ^ k *
        ((2 * π) ^ k * |(n : ℝ)| ^ k / T ^ k * ‖fourierCoeffOn _ (fun x : ℝ ↦ f x) n‖) := by
          field_simp
      _ ≤ T ^ k / (2 * π) ^ k * M := by gcongr

/-- The Fourier monomial `z ↦ e^{2πinz/T}`, extended to all of `ℂ`, is `T`-periodic. -/
theorem periodic_cexp_two_pi_mul_I_mul_div (n : ℤ) :
    Function.Periodic (fun z : ℂ ↦ cexp (2 * π * I * n * z / T)) T := fun z ↦ by
  have hTc : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT.out.ne'
  dsimp only
  rw [show 2 * π * I * n * (z + T) / T = 2 * π * I * n * z / T + n * (2 * π * I) by
    field_simp, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

omit hT in
/-- **Shifting a period integral off the real axis.** If `h` is `T`-periodic and holomorphic on the
closed strip `|Im z| ≤ |y|`, then its integral over a period of the real axis equals its integral
over a period of the horizontal line `Im z = y`. The integrals over the two vertical sides of the
rectangle with corners `0` and `T + y i` cancel by periodicity, so this is Cauchy's theorem for
that rectangle. -/
theorem integral_eq_integral_add_mul_I_of_differentiableOn_strip {h : ℂ → ℂ} {y : ℝ}
    (hper : ∀ z : ℂ, |z.im| ≤ |y| → h (z + T) = h z)
    (hh : DifferentiableOn ℂ h {z | |z.im| ≤ |y|}) :
    ∫ x in (0 : ℝ)..T, h x = ∫ x in (0 : ℝ)..T, h (x + y * I) := by
  have hmem {t : ℝ} (ht : t ∈ [[0, y]]) : |t| ≤ |y| := by
    simpa using Set.abs_sub_left_of_mem_uIcc ht
  have key : (∫ x in (0 : ℝ)..T, h x) - (∫ x in (0 : ℝ)..T, h (x + y * I)) +
      I • (∫ t in (0 : ℝ)..y, h (T + t * I)) - I • ∫ t in (0 : ℝ)..y, h (t * I) = 0 := by
    simpa using integral_boundary_rect_eq_zero_of_differentiableOn h 0 (T + y * I)
      (hh.mono fun z hz ↦ hmem (by simpa using hz.2))
  have hside : ∫ t in (0 : ℝ)..y, h (T + t * I) = ∫ t in (0 : ℝ)..y, h (t * I) :=
    intervalIntegral.integral_congr fun t ht ↦ by
      rw [add_comm]
      exact hper _ (by simpa using hmem ht)
  rw [hside, add_sub_cancel_right, sub_eq_zero] at key
  exact key

/-- **Exponential decay of the Fourier coefficients of a function holomorphic in a strip.** If
`f : AddCircle T → ℂ` is the restriction to `ℝ` of a function `g` which is `T`-periodic and
holomorphic on the closed strip `|Im z| ≤ δ`, and bounded there by `M`, then
`‖fourierCoeff f n‖ ≤ M e^{-2π |n| δ / T}`. -/
theorem norm_fourierCoeff_le_of_differentiableOn_strip {f : AddCircle T → ℂ} {g : ℂ → ℂ}
    {δ M : ℝ} (hδ : 0 ≤ δ) (hfg : ∀ x : ℝ, f x = g x)
    (hper : ∀ z : ℂ, |z.im| ≤ δ → g (z + T) = g z)
    (hg : DifferentiableOn ℂ g {z | |z.im| ≤ δ}) (hM : ∀ z : ℂ, |z.im| ≤ δ → ‖g z‖ ≤ M)
    (n : ℤ) : ‖fourierCoeff f n‖ ≤ M * Real.exp (-(2 * π * |(n : ℝ)| * δ / T)) := by
  have hT0 : 0 < T := hT.out
  -- The contour of the coefficient integral is shifted to the horizontal line `Im z = y`, on the
  -- side of the real axis where the Fourier monomial `e^{-2πinz/T}` is small.
  obtain ⟨y, hyδ, hny⟩ : ∃ y : ℝ, |y| = δ ∧ (n : ℝ) * y = -(|(n : ℝ)| * δ) := by
    rcases le_or_gt 0 (n : ℝ) with hn | hn
    · exact ⟨-δ, by simp [abs_of_nonneg hδ], by rw [abs_of_nonneg hn]; ring⟩
    · exact ⟨δ, abs_of_nonneg hδ, by rw [abs_of_neg hn]; ring⟩
  set h : ℂ → ℂ := fun z ↦ cexp (2 * π * I * (-n : ℤ) * z / T) * g z with hh
  have hshift : ∫ x in (0 : ℝ)..T, h x = ∫ x in (0 : ℝ)..T, h (x + y * I) := by
    refine integral_eq_integral_add_mul_I_of_differentiableOn_strip (fun z hz ↦ ?_)
      ((differentiable_exp.comp (by fun_prop)).differentiableOn.mul (hyδ ▸ hg))
    simp only [hh, periodic_cexp_two_pi_mul_I_mul_div (-n) z, hper z (hyδ ▸ hz)]
  -- On the shifted line, `|e^{-2πinz/T}| = e^{2πny/T} = e^{-2π|n|δ/T}`.
  have hbound (x : ℝ) : ‖h (x + y * I)‖ ≤ M * Real.exp (-(2 * π * |(n : ℝ)| * δ / T)) := by
    have hre : (2 * π * I * (-n : ℤ) * (x + y * I) / T).re = -(2 * π * |(n : ℝ)| * δ / T) := by
      rw [show 2 * π * I * (-n : ℤ) * (x + y * I) / T =
          ((2 * π * (n * y) / T : ℝ) : ℂ) + ((-(2 * π * n * x / T) : ℝ) : ℂ) * I by
        push_cast; linear_combination (-(2 * π * n * y / T : ℂ)) * I_sq, hny]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero]
      ring
    rw [hh, norm_mul, norm_exp, hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ (by simp [hyδ])) (Real.exp_pos _).le
  -- The coefficient is `T⁻¹ ∫₀ᵀ h`, which is now bounded by the shifted integral.
  rw [fourierCoeff_eq_fourierCoeffOn 0, fourierCoeffOn_eq_integral]
  have hint : ∫ x in (0 : ℝ)..0 + T, fourier (-n) (x : AddCircle (0 + T - 0)) • f x =
      ∫ x in (0 : ℝ)..T, h x := by
    rw [zero_add]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    rw [fourier_coe_apply, hfg, smul_eq_mul, hh]
    congr 2
    push_cast
    ring
  rw [hint, hshift, norm_smul]
  calc _ ≤ ‖1 / (0 + T - 0)‖ * (M * Real.exp (-(2 * π * |(n : ℝ)| * δ / T)) * |T - 0|) := by
        gcongr
        exact intervalIntegral.norm_integral_le_of_norm_le_const fun x _ ↦ hbound x
    _ = M * Real.exp (-(2 * π * |(n : ℝ)| * δ / T)) := by
        simp [abs_of_pos hT0]
        field_simp

end Circle

end TauCeti
