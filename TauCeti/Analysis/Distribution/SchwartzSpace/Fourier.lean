/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Derivatives of Schwartz functions on the Fourier side

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

Fourier multipliers are additive in their symbol and commute with the Laplacian.

For the inverse Fourier transform, iterating Mathlib's `SchwartzMap.fourierInv_lineDerivOp_eq`
gives `𝓕⁻ (∂_m^N σ) x = (-2πi ⟪x, m⟫) ^ N 𝓕⁻ σ x`, and Mathlib's `norm_fourier_toL2_eq` gives
Plancherel's theorem `‖𝓕⁻ f‖_{L²} = ‖f‖_{L²}`.

## Main declarations

* `SchwartzMap.fourierMultiplierCLM_add`: Fourier multipliers are additive in the symbol.
* `SchwartzMap.fourierMultiplierCLM_laplacian`: Fourier multipliers commute with the Laplacian.

* `SchwartzMap.fourier_lineDerivOp_lineDerivOp_apply`: the Fourier transform of a second
  directional derivative.
* `SchwartzMap.fourier_laplacian_apply`: the Fourier transform of the Laplacian.
* `SchwartzMap.fourierInv_iterate_lineDerivOp_apply`: the inverse Fourier transform of an
  iterated directional derivative, `𝓕⁻ (∂_m^N σ) x = (-2πi ⟪x, m⟫) ^ N 𝓕⁻ σ x`.
* `SchwartzMap.norm_fourierInv_iterate_lineDerivOp_sq`: its consequence for squared norms,
  `‖𝓕⁻ (∂_m^N σ) x‖² = (2π) ^ (2N) ⟪x, m⟫ ^ (2N) ‖𝓕⁻ σ x‖²`.
* `SchwartzMap.norm_fourierInv_toL2_eq`: Plancherel's theorem for the inverse Fourier transform.
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

section FourierMultiplier

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
  [SMulCommClass ℂ 𝕜 F]

/-- Fourier multipliers are additive in the symbol. -/
theorem fourierMultiplierCLM_add {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg₁ hg₂]

variable [CompleteSpace F]

/-- Fourier multipliers commute with the Laplacian. -/
theorem fourierMultiplierCLM_laplacian {g : E → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (Δ f) = Δ (fourierMultiplierCLM F g f) := by
  have hn : (fun ξ : E ↦ ‖ξ‖ ^ 2).HasTemperateGrowth := by fun_prop
  -- Commute the two symbols before transporting the identity through the Laplacian formula.
  have hcomm : fourierMultiplierCLM F g
      (fourierMultiplierCLM F (fun ξ : E ↦ ‖ξ‖ ^ 2) f) =
      fourierMultiplierCLM F (fun ξ : E ↦ ‖ξ‖ ^ 2) (fourierMultiplierCLM F g f) := by
    have hn𝕜 : (fun ξ : E ↦ RCLike.ofReal (K := 𝕜) (‖ξ‖ ^ 2)).HasTemperateGrowth := by
      fun_prop
    simp only [← fourierMultiplierCLM_ofReal 𝕜 hn]
    simp only [fourierMultiplierCLM_fourierMultiplierCLM_apply hg hn𝕜,
      fourierMultiplierCLM_fourierMultiplierCLM_apply hn𝕜 hg, mul_comm g]
  simpa only [laplacian_eq_fourierMultiplierCLM, ContinuousLinearMap.map_smul_of_tower]
    using congrArg (fun q ↦ -((2 * π) ^ 2) • q) hcomm

end FourierMultiplier

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

/-- Differentiating `N` times along `m` multiplies the inverse Fourier transform by
`(-2πi ⟪x, m⟫) ^ N`. -/
theorem fourierInv_iterate_lineDerivOp_apply (σ : 𝓢(E, F)) (m : E) (N : ℕ) (x : E) :
    𝓕⁻ ((∂_{m})^[N] σ) x = (-(2 * π * Complex.I) * ⟪x, m⟫) ^ N • 𝓕⁻ σ x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hm : (inner ℝ · m : E → ℝ).HasTemperateGrowth := by fun_prop
    rw [Function.iterate_succ_apply', fourierInv_lineDerivOp_eq, smul_apply,
      smulLeftCLM_apply_apply hm, ih, pow_succ, ← Complex.coe_smul, smul_smul, smul_smul]
    congr 1
    ring

/-- Differentiating `N` times along `m` multiplies the squared norm of the inverse Fourier
transform by `(2π) ^ (2N) ⟪x, m⟫ ^ (2N)`. -/
theorem norm_fourierInv_iterate_lineDerivOp_sq (σ : 𝓢(E, F)) (m : E) (N : ℕ) (x : E) :
    ‖𝓕⁻ ((∂_{m})^[N] σ) x‖ ^ 2 = (2 * π) ^ (2 * N) * (⟪x, m⟫ ^ (2 * N) * ‖𝓕⁻ σ x‖ ^ 2) := by
  rw [fourierInv_iterate_lineDerivOp_apply, norm_smul, mul_pow, norm_pow, norm_mul, norm_neg,
    Complex.norm_real, Complex.norm_mul, Complex.norm_I, Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    ← (even_two_mul N).pow_abs ⟪x, m⟫]
  ring

end normed

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Plancherel's theorem** for the inverse Fourier transform of Schwartz functions. -/
@[simp]
theorem norm_fourierInv_toL2_eq (f : 𝓢(E, F)) : ‖(𝓕⁻ f).toLp 2‖ = ‖f.toLp 2‖ := by
  rw [← norm_fourier_toL2_eq (𝓕⁻ f), FourierTransform.fourier_fourierInv_eq]

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
