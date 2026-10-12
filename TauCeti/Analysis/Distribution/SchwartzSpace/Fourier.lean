/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Second derivatives of Schwartz functions on the Fourier side

The Fourier transform turns the directional derivative `∂_v` on Schwartz space into
multiplication by `2πi ⟪ξ, v⟫` (Mathlib's `SchwartzMap.fourier_lineDerivOp_eq`). This file
records the pointwise consequences for second-order operators: with Mathlib's normalization of the
Fourier transform,

* `𝓕 (∂_v ∂_w u) ξ = -(2π)² ⟪ξ, v⟫ ⟪ξ, w⟫ 𝓕 u ξ`, and
* `𝓕 (Δ u) ξ = -(2π)² ‖ξ‖² 𝓕 u ξ`.

Since `∑ᵢ ∑ⱼ ⟪ξ, bᵢ⟫² ⟪ξ, bⱼ⟫² = ‖ξ‖⁴` for an orthonormal basis `b`, Plancherel's theorem turns
these into the identity

`∑ᵢ ∑ⱼ ‖∂_{bᵢ} ∂_{bⱼ} u‖²_{L²} = ‖Δ u‖²_{L²}`,

so the Laplacian controls the whole Hessian of `u` in `L²`. This is the `p = 2` case of the
Calderón–Zygmund estimate `‖D²u‖_{Lᵖ} ≤ C ‖Δu‖_{Lᵖ}`, and the `L²` input to elliptic regularity
for the Laplacian on `ℝⁿ`.

## Main declarations

* `SchwartzMap.fourier_lineDerivOp_lineDerivOp_apply`: the Fourier transform of a second
  directional derivative.
* `SchwartzMap.fourier_laplacian_apply`: the Fourier transform of the Laplacian.
* `SchwartzMap.sum_sum_norm_toLp_lineDerivOp_lineDerivOp_sq`: the squared `L²` norms of the
  second derivatives along an orthonormal basis sum to the squared `L²` norm of the Laplacian.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.4.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace Real Laplacian LineDeriv
open FourierTransform MeasureTheory

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

section normed

variable [NormedSpace ℂ F]

/-- The Fourier transform of the second directional derivative `∂_v ∂_w u` of a Schwartz function
is `𝓕 u` multiplied by `-(2π)² ⟪ξ, v⟫ ⟪ξ, w⟫`. -/
theorem fourier_lineDerivOp_lineDerivOp_apply (u : 𝓢(E, F)) (v w ξ : E) :
    𝓕 (∂_{v} (∂_{w} u)) ξ = (-(2 * π) ^ 2 * (⟪ξ, v⟫ * ⟪ξ, w⟫)) • 𝓕 u ξ := by
  have hv : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
  have hw : (inner ℝ · w : E → ℝ).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq, smul_apply, smulLeftCLM_apply_apply hv, fourier_lineDerivOp_eq,
    smul_apply, smulLeftCLM_apply_apply hw]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  push_cast
  linear_combination (2 * π : ℂ) ^ 2 * (⟪ξ, v⟫ : ℂ) * ⟪ξ, w⟫ * Complex.I_sq

/-- The Fourier transform of the Laplacian of a Schwartz function is `𝓕 u` multiplied by
`-(2π)² ‖ξ‖²`. -/
theorem fourier_laplacian_apply (u : 𝓢(E, F)) (ξ : E) :
    𝓕 (Δ u) ξ = (-(2 * π) ^ 2 * ‖ξ‖ ^ 2) • 𝓕 u ξ := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_sum b, FourierTransform.fourier_sum, sum_apply]
  simp only [fourier_lineDerivOp_lineDerivOp_apply, ← Finset.sum_smul, ← Finset.mul_sum, ← sq,
    b.sum_sq_inner_left]

end normed

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The Laplacian controls the Hessian in `L²`: for a Schwartz function `u` and an orthonormal
basis `b`, `∑ᵢ ∑ⱼ ‖∂_{bᵢ} ∂_{bⱼ} u‖²_{L²} = ‖Δ u‖²_{L²}`. -/
theorem sum_sum_norm_toLp_lineDerivOp_lineDerivOp_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u : 𝓢(E, F)) :
    ∑ i, ∑ j, ‖(∂_{b i} (∂_{b j} u)).toLp 2‖ ^ 2 = ‖(Δ u).toLp 2‖ ^ 2 := by
  -- By Plancherel, each squared `L²` norm is the integral of `‖𝓕 g‖²`; the pointwise identity
  -- `∑ᵢ ∑ⱼ ⟪ξ, bᵢ⟫² ⟪ξ, bⱼ⟫² = ‖ξ‖⁴` then matches the integrands.
  have hF (g : 𝓢(E, F)) : ‖g.toLp 2‖ ^ 2 = ∫ ξ, ‖𝓕 g ξ‖ ^ 2 := by
    rw [← Lp.norm_fourier_eq, toLp_fourier_eq, norm_toLp' two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, ← Real.rpow_two,
      ← Real.rpow_mul (integral_nonneg fun _ ↦ by positivity)]
    norm_num
  have hint (g : 𝓢(E, F)) : Integrable (fun ξ ↦ ‖𝓕 g ξ‖ ^ 2) :=
    ((𝓕 g).memLp 2).integrable_norm_pow two_ne_zero
  simp only [hF]
  simp_rw [← integral_finsetSum _ fun i _ ↦ hint _]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  have hsum : ∑ i, ∑ j, (⟪ξ, b i⟫ * ⟪ξ, b j⟫) ^ 2 = (‖ξ‖ ^ 2) ^ 2 := by
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, b.sum_sq_inner_left, sq]
  simp only [fourier_lineDerivOp_lineDerivOp_apply, fourier_laplacian_apply, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, ← hsum, Finset.mul_sum, Finset.sum_mul]

end SchwartzMap
