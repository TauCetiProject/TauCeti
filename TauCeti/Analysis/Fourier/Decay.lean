/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle

import TauCeti.Analysis.Calculus.PeriodicDeriv

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
the Fourier-coefficient Sobolev spaces of the circle.

## Main declarations

* `TauCeti.exists_norm_pow_mul_norm_fourier_le`: for every exponent `k`, the Fourier transform of a
  smooth compactly supported function on a finite-dimensional real inner product space satisfies
  `‖v‖ ^ k * ‖𝓕 f v‖ ≤ C` for some `C > 0`.
* `TauCeti.exists_abs_pow_mul_norm_fourierCoeff_le`: if `f : AddCircle T → ℂ` is `C^k` as a
  periodic function on `ℝ`, then `|n| ^ k * ‖fourierCoeff f n‖ ≤ C` for some `C`.
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

/-- The Fourier coefficients of a function on `AddCircle T` are those of its lift to `ℝ` on the
period interval `(0, T]`. -/
private theorem fourierCoeff_eq_fourierCoeffOn (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff f n = fourierCoeffOn (lt_add_of_pos_right 0 hT.out) (fun x : ℝ ↦ f x) n := by
  rw [← fourierCoeff_liftIoc_eq]
  congr 1
  funext x
  simp [AddCircle.liftIoc, AddCircle.coe_equivIoc]

/-- Each derivative of a `C^k` periodic function multiplies its nonzero-frequency Fourier
coefficients by `2πin / T`. -/
private theorem fourierCoeffOn_iteratedDeriv {f : AddCircle T → ℂ} {k : ℕ}
    (hf : ContDiff ℝ k fun x : ℝ ↦ f x) {n : ℤ} (hn : n ≠ 0) {j : ℕ} (hj : j ≤ k) :
    fourierCoeffOn (lt_add_of_pos_right 0 hT.out) (iteratedDeriv j fun x : ℝ ↦ f x) n =
      (2 * π * I * n / T) ^ j *
        fourierCoeffOn (lt_add_of_pos_right 0 hT.out) (fun x : ℝ ↦ f x) n := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hd := hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)
    have h := fourierCoeffOn_of_hasDerivAt (lt_add_of_pos_right 0 hT.out) hn
      (f := iteratedDeriv j fun x : ℝ ↦ f x) (f' := iteratedDeriv (j + 1) fun x : ℝ ↦ f x)
      (fun x _ ↦ by simpa [iteratedDeriv_succ] using (hd x).hasDerivAt)
      ((hf.continuous_iteratedDeriv (j + 1) (by exact_mod_cast hj)).intervalIntegrable _ _)
    have hper : Function.Periodic (fun x : ℝ ↦ f x) T := fun x ↦ by simp
    rw [hper.iteratedDeriv j 0, sub_self, mul_zero, zero_sub, ih (by omega)] at h
    have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.2 hT.out.ne'
    have hc : (2 * π * I * n : ℂ) ≠ 0 := by simp [hn, Real.pi_ne_zero, I_ne_zero]
    rw [pow_succ, mul_comm _ (2 * π * I * n / T), mul_assoc, h]
    push_cast
    field_simp
    ring

/-- A pointwise bound on a function over the period interval bounds its Fourier coefficients. -/
private theorem norm_fourierCoeffOn_le {g : ℝ → ℂ} {M : ℝ}
    (hM : ∀ x ∈ Set.Icc 0 (0 + T), ‖g x‖ ≤ M) (n : ℤ) :
    ‖fourierCoeffOn (lt_add_of_pos_right 0 hT.out) g n‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 0 + T)
    (f := fun x : ℝ ↦ fourier (-n) (x : AddCircle (0 + T - 0)) • g x) (C := M) fun x hx ↦ by
      simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      have hx' := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by linarith [hT.out])] at hx'
      exact hM x hx'
  simp only [zero_add, sub_zero, abs_of_pos hT.out] at h ⊢
  rw [norm_div, norm_one, Real.norm_of_nonneg hT.out.le]
  have hT := hT.out
  calc 1 / T * _ ≤ 1 / T * (M * T) := by gcongr
    _ = M := by field_simp

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
  have hbound := norm_fourierCoeffOn_le hM n
  rw [fourierCoeff_eq_fourierCoeffOn]
  rcases eq_or_ne n 0 with rfl | hn
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hbound
    · simp only [Int.cast_zero, abs_zero, zero_pow hk.ne', zero_mul]
      have := hT.out
      positivity
  · rw [fourierCoeffOn_iteratedDeriv hf hn le_rfl, norm_mul, norm_pow] at hbound
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

end Circle

end TauCeti
