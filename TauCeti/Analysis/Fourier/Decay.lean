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
is used in when it weights a comparison test.

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
* `TauCeti.exists_abs_pow_mul_norm_fourierCoeff_le`: if `f : AddCircle T → ℂ` is `C^k` as a
  periodic function on `ℝ`, then `|n| ^ k * ‖fourierCoeff f n‖ ≤ C` for some `C`.
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
  have hTc : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT0.ne'
  -- The contour of the coefficient integral is shifted to the horizontal line `Im z = y`, on the
  -- side of the real axis where the Fourier monomial `e^{-2πinz/T}` is small.
  obtain ⟨y, hyδ, hny⟩ : ∃ y : ℝ, |y| = δ ∧ (n : ℝ) * y = -(|(n : ℝ)| * δ) := by
    rcases le_or_gt 0 (n : ℝ) with hn | hn
    · exact ⟨-δ, by simp [abs_of_nonneg hδ], by rw [abs_of_nonneg hn]; ring⟩
    · exact ⟨δ, abs_of_nonneg hδ, by rw [abs_of_neg hn]; ring⟩
  set h : ℂ → ℂ := fun z ↦ cexp (-(2 * π * I * n * z / T)) * g z with hh
  have hmem {t : ℝ} (ht : t ∈ [[0, y]]) : |t| ≤ δ := by
    rw [← hyδ]
    rcases Set.mem_uIcc.1 ht with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact abs_le_abs h₂ (by linarith)
    · rw [abs_of_nonpos h₂, abs_of_nonpos (h₁.trans h₂)]; linarith
  have hrect : DifferentiableOn ℂ h ([[(0 : ℂ).re, (T + y * I).re]] ×ℂ
      [[(0 : ℂ).im, (T + y * I).im]]) := by
    refine ((differentiable_exp.comp (by fun_prop)).differentiableOn.mul hg).mono fun z hz ↦ ?_
    simp only [mem_reProdIm, zero_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add] at hz
    exact hmem hz.2
  -- The integrals of `h` over the two vertical sides of the rectangle agree, by periodicity.
  have hside : ∫ t in (0 : ℝ)..y, h (T + t * I) = ∫ t in (0 : ℝ)..y, h (0 + t * I) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    have hexp : cexp (-(2 * π * I * n * (T + t * I) / T)) =
        cexp (-(2 * π * I * n * (t * I) / T)) := by
      rw [show -(2 * π * I * n * (T + t * I) / T) =
          -(2 * π * I * n * (t * I) / T) + ((-n : ℤ) : ℂ) * (2 * π * I) by
        push_cast; field_simp; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    have hg' : g (T + t * I) = g (t * I) := by
      rw [add_comm]
      exact hper _ (by simpa using hmem ht)
    simp only [hh, zero_add, hexp, hg']
  -- Cauchy's theorem for the rectangle with corners `0` and `T + y i`.
  have hshift : ∫ x in (0 : ℝ)..T, h x = ∫ x in (0 : ℝ)..T, h (x + y * I) := by
    have key := integral_boundary_rect_eq_zero_of_differentiableOn h 0 (T + y * I) hrect
    simp only [zero_re, zero_im, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
      sub_zero, mul_one, add_im, mul_im, zero_add, add_zero, ofReal_zero, zero_mul] at key
    rw [hside] at key
    simp only [zero_add] at key
    linear_combination key
  -- On the shifted line, `|e^{-2πinz/T}| = e^{2πny/T} = e^{-2π|n|δ/T}`.
  have hbound (x : ℝ) : ‖h (x + y * I)‖ ≤ M * Real.exp (-(2 * π * |(n : ℝ)| * δ / T)) := by
    have hre : (-(2 * π * I * n * (x + y * I) / T)).re = -(2 * π * |(n : ℝ)| * δ / T) := by
      rw [show -(2 * π * I * n * (x + y * I) / T) =
          ((2 * π * (n * y) / T : ℝ) : ℂ) + ((-(2 * π * n * x / T) : ℝ) : ℂ) * I by
        push_cast; field_simp; ring_nf; rw [I_sq]; ring, hny]
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
