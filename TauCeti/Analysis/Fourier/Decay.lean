/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.AddCircle

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
open scoped Real

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

end Circle

end TauCeti
