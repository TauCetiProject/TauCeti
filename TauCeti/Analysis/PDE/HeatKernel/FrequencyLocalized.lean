/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
import Mathlib.Analysis.Fourier.Convolution
import TauCeti.Analysis.Bochner.Fourier.Nonneg
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.BandLimited
import TauCeti.Analysis.PDE.HeatKernel.Derivatives
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic

/-!
# The heat flow of frequency-localized functions

On a finite-dimensional real inner product space `E` of dimension `n`, the heat semigroup
`e^{tΔ}` is the Fourier multiplier with symbol `exp(-4π² t ‖ξ‖²)`. On a function whose Fourier
transform lives in the annulus `ν r ≤ ‖ξ‖ ≤ ν R`, `r > 0`, this symbol is at most
`exp(-4π² r² ν² t)`, and the heat flow decays exponentially in `ν² t` in every `Lᵖ` norm:

`‖e^{tΔ} f‖_p ≤ C exp(-π² r² ν² t / 4) ‖f‖_p`,

with `C` depending only on `r`, `R` and `E`. This is the heat estimate for the dyadic blocks of
the Littlewood–Paley decomposition: for `j ≥ 1` the block `Δⱼ f` has frequencies of size `2^j`,
so `‖e^{tΔ} Δⱼ f‖_p ≤ C exp(-c 4^j t) ‖Δⱼ f‖_p`. It is how the heat semigroup gains regularity
on Besov and Hölder–Zygmund spaces, `‖e^{tΔ} f‖_{𝒞^{s + 2σ}} ≤ C t^{-σ} ‖f‖_{𝒞^s}` for
`σ ≥ 0` and `0 < t ≤ 1`.

The proof writes `e^{tΔ} f` as the convolution of `f` with the kernel `𝓕⁻ σ`, where
`σ ξ = χ (ν⁻¹ ξ) exp(-4π² t ‖ξ‖²)` and `χ` is a smooth cutoff equal to `1` on the annulus
`r ≤ ‖ξ‖ ≤ R` and vanishing near the origin. The derivatives of `σ` of every order are
`O(ν^{-k} exp(-π² r² ν² t / 4))`: on the support of `χ (ν⁻¹ ·)`, each derivative of the Gaussian
costs a factor `√t (1 + √t ‖ξ‖)`, which the remaining Gaussian factor absorbs. The weighted
Plancherel bound for kernels of band-limited symbols then gives
`∫ ‖𝓕⁻ σ‖ ≤ C exp(-π² r² ν² t / 4)`, and Young's inequality finishes the estimate.

## Main declarations

* `TauCeti.exists_integral_norm_fourierInv_mul_exp_le`: the `L¹` norm of the kernel of the
  frequency-localized heat multiplier `χ (ν⁻¹ ξ) exp(-4π² t ‖ξ‖²)` is
  `O(exp(-π² r² ν² t))` when `χ` vanishes on the ball of radius `r`.
* `TauCeti.exists_norm_heatSemigroup_toLp_le_of_support_fourier_subset`: the heat semigroup on
  a Schwartz function with Fourier transform in the annulus `ν r ≤ ‖ξ‖ ≤ ν R` decays like
  `exp(-π² r² ν² t / 4)` in `Lᵖ`.
* `TauCeti.exists_norm_heatSemigroup_toLp_fourierMultiplierCLM_inhomogeneousLittlewoodPaley_le`:
  the heat estimate for the Littlewood–Paley blocks `Δⱼ`, `j ≥ 1`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Real Set Function FourierTransform SchwartzMap ContinuousLinearMap
open scoped ContDiff Convolution SchwartzMap LineDeriv NNReal ENNReal ComplexConjugate Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The kernel of the frequency-localized heat multiplier -/

section Kernel

variable {χ : E → ℝ} {r : ℝ}

/-- **Derivative bounds for the heat multiplier cut off away from the origin, at unit scale.**
If `χ` is smooth, compactly supported and vanishes on the ball of radius `r > 0`, every
derivative of `χ η exp(-4π² τ ‖η‖²)` is `O(exp(-π² r² τ))`, uniformly in `τ ≥ 0`. -/
private theorem exists_norm_iteratedFDeriv_mul_exp_le (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hr : 0 < r) (hχr : ∀ ξ, ‖ξ‖ < r → χ ξ = 0) (k : ℕ) :
    ∃ A, ∀ τ, 0 ≤ τ → ∀ η : E,
      ‖iteratedFDeriv ℝ k (fun η ↦ χ η * rexp (-(4 * π ^ 2 * τ * ‖η‖ ^ 2))) η‖ ≤
        A * rexp (-(π ^ 2 * r ^ 2 * τ)) := by
  choose M hM using fun i ↦ ((hχ.continuous_iteratedFDeriv (m := i)
    (by exact_mod_cast le_top)).bounded_above_of_compact_support (hχc.iteratedFDeriv i))
  choose G hG using exists_norm_iteratedFDeriv_exp_neg_mul_norm_sq_le (E := E)
  -- `√τ ^ j exp(-π² r² τ)` is bounded, by `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le` at `√τ`.
  set B : ℕ → ℝ := fun j ↦ j.factorial / (π ^ 2 * r ^ 2 / 2) ^ j * rexp (π ^ 2 * r ^ 2)
  have hB (j : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) : √τ ^ j * rexp (-(π ^ 2 * r ^ 2 * τ)) ≤ B j := by
    have h := one_add_pow_mul_exp_neg_mul_sq_le (by positivity : 0 < π ^ 2 * r ^ 2) j
      (sqrt_nonneg τ)
    rw [sq_sqrt hτ, neg_mul] at h
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sqrt_nonneg τ)
      (le_add_of_nonneg_left zero_le_one) j) (exp_pos _).le).trans h
  have hM0 (i : ℕ) : 0 ≤ M i := (norm_nonneg _).trans (hM i 0)
  have hG0 (j : ℕ) : 0 ≤ G j := by
    have h := (norm_nonneg _).trans (hG j 1 zero_le_one 0)
    simpa [(exp_pos _).ne', sqrt_one] using h
  have hB0 (j : ℕ) : 0 ≤ B j := by positivity
  set D : ℕ → ℝ := fun i ↦ k.choose i * M i * (G (k - i) * (2 * π) ^ (k - i) * B (k - i))
  have hD0 (i : ℕ) : 0 ≤ D i := mul_nonneg (mul_nonneg (by positivity) (hM0 i))
    (mul_nonneg (mul_nonneg (hG0 _) (by positivity)) (hB0 _))
  refine ⟨∑ i ∈ Finset.range (k + 1), D i, fun τ hτ η ↦ ?_⟩
  have hg : ContDiff ℝ ∞ fun η : E ↦ rexp (-(4 * π ^ 2 * τ * ‖η‖ ^ 2)) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).neg.exp
  refine (norm_iteratedFDeriv_mul_le hχ hg η (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rcases lt_or_ge ‖η‖ r with hη | hη
  · -- `χ` vanishes near `η`, hence so do its derivatives.
    have h0 : χ =ᶠ[𝓝 η] 0 :=
      Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hη) hχr
    rw [(h0.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply, norm_zero,
      mul_zero, zero_mul]
    exact mul_nonneg (hD0 i) (exp_pos _).le
  -- On `‖η‖ ≥ r` the Gaussian factor is at most `exp(-π² r² τ)²`, and one of the two factors
  -- absorbs the power `√τ ^ (k - i)` produced by the derivatives of the Gaussian.
  have hsq : √(4 * π ^ 2 * τ) = 2 * π * √τ := by
    rw [sqrt_mul (by positivity), sqrt_mul' _ (by positivity), sqrt_sq pi_pos.le,
      show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq zero_le_two]
  have hexp : rexp (-(4 * π ^ 2 * τ * ‖η‖ ^ 2) / 2) ≤
      rexp (-(π ^ 2 * r ^ 2 * τ)) * rexp (-(π ^ 2 * r ^ 2 * τ)) := by
    rw [← exp_add, exp_le_exp]
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hη 2)
      (by positivity : 0 ≤ π ^ 2 * τ)
    linarith
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ η‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun η ↦ rexp (-(4 * π ^ 2 * τ * ‖η‖ ^ 2))) η‖
      ≤ k.choose i * M i * (G (k - i) * (2 * π * √τ) ^ (k - i) *
          (rexp (-(π ^ 2 * r ^ 2 * τ)) * rexp (-(π ^ 2 * r ^ 2 * τ)))) := by
        have h₂ := (hG (k - i) (4 * π ^ 2 * τ) (by positivity) η).trans
          (mul_le_mul_of_nonneg_left hexp (mul_nonneg (hG0 _) (by positivity)))
        rw [hsq] at h₂
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hM i η) (by positivity)) h₂
          (norm_nonneg _) (mul_nonneg (by positivity) (hM0 i))
    _ = k.choose i * M i * (G (k - i) * (2 * π) ^ (k - i) *
          (√τ ^ (k - i) * rexp (-(π ^ 2 * r ^ 2 * τ)))) * rexp (-(π ^ 2 * r ^ 2 * τ)) := by
        ring
    _ ≤ D i * rexp (-(π ^ 2 * r ^ 2 * τ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (hB _ τ hτ) (mul_nonneg (hG0 _) (by positivity))) (mul_nonneg (by positivity) (hM0 i)))
          (exp_pos _).le

/-- The frequency-localized heat multiplier `χ (ν⁻¹ ξ) exp(-4π² t ‖ξ‖²)` is the unit-scale one at
time `ν² t`, evaluated at `ν⁻¹ ξ`. -/
private theorem mul_exp_eq_comp_smul {ν : ℝ} (hν : 0 < ν) (t : ℝ) :
    (fun ξ : E ↦ χ (ν⁻¹ • ξ) * rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2))) =
      fun ξ ↦ (fun η ↦ χ η * rexp (-(4 * π ^ 2 * (ν ^ 2 * t) * ‖η‖ ^ 2))) (ν⁻¹ • ξ) := by
  funext ξ
  simp only [norm_smul, norm_inv, norm_of_nonneg hν.le, mul_pow, inv_pow]
  congr 3
  field_simp

/-- The frequency-localized heat multiplier `χ (ν⁻¹ ξ) exp(-4π² t ‖ξ‖²)`, as a Schwartz function
with complex values. -/
private def cutoffHeatSymbol (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {ν : ℝ}
    (hν : ν ≠ 0) (t : ℝ) : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap
    (f := fun ξ : E ↦ ((χ (ν⁻¹ • ξ) * rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ))
    (((hχc.comp_smul (inv_ne_zero hν)).mul_right).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp ((hχ.comp (contDiff_const_smul _)).mul
      (contDiff_const.mul (contDiff_norm_sq ℝ)).neg.exp))

/-- The values of `cutoffHeatSymbol`. -/
private theorem cutoffHeatSymbol_apply (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    {ν : ℝ} (hν : ν ≠ 0) (t : ℝ) (ξ : E) :
    cutoffHeatSymbol hχ hχc hν t ξ = ((χ (ν⁻¹ • ξ) * rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ) :=
  HasCompactSupport.toSchwartzMap_toFun _ _ _

/-- The derivatives of `cutoffHeatSymbol` are `ν⁻ᵏ` times those of the unit-scale symbol at time
`ν² t`, evaluated at `ν⁻¹ ξ`. -/
private theorem norm_iteratedFDeriv_cutoffHeatSymbol (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {ν : ℝ} (hν : 0 < ν) (t : ℝ) (k : ℕ) (ξ : E) :
    ‖iteratedFDeriv ℝ k (cutoffHeatSymbol hχ hχc hν.ne' t : E → ℂ) ξ‖ = ν⁻¹ ^ k *
      ‖iteratedFDeriv ℝ k (fun η ↦ χ η * rexp (-(4 * π ^ 2 * (ν ^ 2 * t) * ‖η‖ ^ 2)))
        (ν⁻¹ • ξ)‖ := by
  set s₁ : E → ℝ := fun η ↦ χ η * rexp (-(4 * π ^ 2 * (ν ^ 2 * t) * ‖η‖ ^ 2))
  have hs₁ : ContDiff ℝ ∞ s₁ := hχ.mul (contDiff_const.mul (contDiff_norm_sq ℝ)).neg.exp
  have hσ : (cutoffHeatSymbol hχ hχc hν.ne' t : E → ℂ) =
      Complex.ofRealLI ∘ fun ξ ↦ s₁ (ν⁻¹ • ξ) := by
    funext ξ
    rw [cutoffHeatSymbol_apply, comp_apply, Complex.ofRealLI_apply,
      congrFun (mul_exp_eq_comp_smul hν t) ξ]
  have hc : ContDiff ℝ ∞ fun ξ : E ↦ s₁ (ν⁻¹ • ξ) := hs₁.comp (contDiff_const_smul _)
  rw [hσ, Complex.ofRealLI.norm_iteratedFDeriv_comp_left hc.contDiffAt
    (by exact_mod_cast le_top),
    iteratedFDeriv_comp_const_smul _ (hs₁.of_le (by exact_mod_cast le_top))]
  beta_reduce
  rw [norm_smul, norm_pow, norm_inv, norm_of_nonneg hν.le]

/-- If `χ` vanishes outside `closedBall 0 R₀`, then `cutoffHeatSymbol` vanishes outside
`closedBall 0 (ν R₀)`. -/
private theorem support_cutoffHeatSymbol_subset (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) {R₀ : ℝ} (hR₀ : tsupport χ ⊆ closedBall 0 R₀) {ν : ℝ}
    (hν : 0 < ν) (t : ℝ) :
    support (cutoffHeatSymbol hχ hχc hν.ne' t) ⊆ closedBall (0 : E) (ν * R₀) := by
  intro ξ hξ
  have hχξ : χ (ν⁻¹ • ξ) ≠ 0 := fun h ↦ hξ (by simp [cutoffHeatSymbol_apply, h])
  have := hR₀ (subset_tsupport _ hχξ)
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_of_nonneg hν.le,
    inv_mul_le_iff₀ hν] at this
  exact mem_closedBall_zero_iff.2 this

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The kernel of the frequency-localized heat multiplier.** Let `χ` be smooth and compactly
supported, vanishing on the ball of radius `r > 0`. There is a constant `C`, depending only on
`χ`, `r` and `E`, such that for every frequency scale `ν > 0` and time `t ≥ 0` the inverse
Fourier transform of the symbol `σ ξ = χ (ν⁻¹ ξ) exp(-4π² t ‖ξ‖²)` satisfies

`∫ ‖𝓕⁻ σ x‖ dx ≤ C exp(-π² r² ν² t)`. -/
theorem exists_integral_norm_fourierInv_mul_exp_le (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hr : 0 < r) (hχr : ∀ ξ, ‖ξ‖ < r → χ ξ = 0) :
    ∃ C, ∀ ν, 0 < ν → ∀ t, 0 ≤ t →
      ∫ x, ‖𝓕⁻ (fun ξ : E ↦ ((χ (ν⁻¹ • ξ) * rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) x‖ ≤
        C * rexp (-(π ^ 2 * r ^ 2 * (ν ^ 2 * t))) := by
  set N : ℕ := finrank ℝ E + 1
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨C₁, -, hC⟩ := SchwartzMap.exists_integral_norm_fourierInv_le_of_support_subset (H := ℂ)
    b (by omega : finrank ℝ E < 2 * N)
  obtain ⟨A₀, hA₀⟩ := exists_norm_iteratedFDeriv_mul_exp_le hχ hχc hr hχr 0
  obtain ⟨A₁, hA₁⟩ := exists_norm_iteratedFDeriv_mul_exp_le hχ hχc hr hχr N
  obtain ⟨R₀, hR₀⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 1
  have hR : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  set A : ℝ := max A₀ (A₁ * R ^ N)
  refine ⟨C₁ * A, fun ν hν t ht ↦ ?_⟩
  set e : ℝ := rexp (-(π ^ 2 * r ^ 2 * (ν ^ 2 * t)))
  set σ : 𝓢(E, ℂ) := cutoffHeatSymbol hχ hχc hν.ne' t
  have hσ : 𝓕⁻ (fun ξ : E ↦ ((χ (ν⁻¹ • ξ) * rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)) =
      ⇑(𝓕⁻ σ : 𝓢(E, ℂ)) := by
    rw [fourierInv_coe, funext (cutoffHeatSymbol_apply hχ hχc hν.ne' t)]
  rw [hσ]
  -- `σ` vanishes outside the ball of radius `ν R`, is bounded by `A₀ e`, and its `N`-th
  -- derivatives are bounded by `A₁ e ν⁻ᴺ = A₁ R^N e (ν R)⁻ᴺ`.
  refine (hC σ (t := ν * R) (A := A * e) (mul_pos hν hR)
    ((support_cutoffHeatSymbol_subset hχ hχc hR₀ hν t).trans
      (closedBall_subset_closedBall (by gcongr; exact le_max_left _ _)))
    (fun ξ ↦ ?_) (fun i ξ ↦ ?_)).trans (le_of_eq (mul_assoc _ _ _).symm)
  · rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ), norm_iteratedFDeriv_cutoffHeatSymbol hχ hχc hν,
      pow_zero, one_mul]
    exact (hA₀ (ν ^ 2 * t) (by positivity) (ν⁻¹ • ξ)).trans (by gcongr; exact le_max_left _ _)
  · rw [← LineDeriv.iteratedLineDerivOp_const_eq_iter_lineDerivOp,
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    refine ((iteratedFDeriv ℝ N (σ : E → ℂ) ξ).le_opNorm _).trans ?_
    simp only [b.orthonormal.1 i, Finset.prod_const_one, mul_one]
    rw [norm_iteratedFDeriv_cutoffHeatSymbol hχ hχc hν, mul_pow, div_eq_mul_inv, mul_inv,
      ← inv_pow, ← inv_pow]
    calc ν⁻¹ ^ N * ‖iteratedFDeriv ℝ N (fun η ↦ χ η *
          rexp (-(4 * π ^ 2 * (ν ^ 2 * t) * ‖η‖ ^ 2))) (ν⁻¹ • ξ)‖ ≤ ν⁻¹ ^ N * (A₁ * e) :=
          mul_le_mul_of_nonneg_left (hA₁ (ν ^ 2 * t) (by positivity) (ν⁻¹ • ξ)) (by positivity)
      _ = A₁ * R ^ N * e * (ν⁻¹ ^ N * R⁻¹ ^ N) := by
          rw [inv_pow R N]
          field_simp
      _ ≤ A * e * (ν⁻¹ ^ N * R⁻¹ ^ N) := by gcongr; exact le_max_right _ _

end Kernel

/-! ### The heat flow of a function with frequencies in an annulus -/

section HeatFlow

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- If the symbol `σ` agrees with the heat multiplier `exp(-4π² t ‖ξ‖²)` wherever `𝓕 f ≠ 0`, then
the heat flow of `f` is the convolution of `f` with the kernel `𝓕⁻ σ`. -/
private theorem heatKernel_convolution_eq_fourierInv_convolution {σ : 𝓢(E, ℂ)} {t : ℝ}
    (ht : 0 < t) {f : 𝓢(E, F)}
    (hσ : ∀ ξ, 𝓕 (f : E → F) ξ ≠ 0 → σ ξ = rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2))) :
    heatKernel t ⋆ (f : E → F) = ⇑(𝓕⁻ σ : 𝓢(E, ℂ)) ⋆[lsmul ℂ ℂ] (f : E → F) := by
  set w : 𝓢(E, F) := SchwartzMap.convolution (lsmul ℂ ℂ) (𝓕⁻ σ) f
  have hw : (w : E → F) = ⇑(𝓕⁻ σ : 𝓢(E, ℂ)) ⋆[lsmul ℂ ℂ] (f : E → F) :=
    funext (convolution_apply _ _ f)
  have hK : Integrable (fun x : E ↦ (heatKernel t x : ℂ)) := (integrable_heatKernel ht).ofReal
  have hu : heatKernel t ⋆ (f : E → F) =
      (fun x : E ↦ (heatKernel t x : ℂ)) ⋆[lsmul ℂ ℂ] (f : E → F) := by
    funext x
    simp only [convolution_def, lsmul_apply, Complex.coe_smul]
  have hFw : 𝓕 (w : E → F) = fun ξ ↦ σ ξ • 𝓕 (f : E → F) ξ := by
    funext ξ
    rw [hw, Real.fourier_smul_convolution_eq (𝓕⁻ σ).integrable f.integrable, ← fourier_coe,
      FourierTransform.fourier_fourierInv_eq]
  have hFu : 𝓕 (heatKernel t ⋆ (f : E → F)) = 𝓕 (w : E → F) := by
    rw [hFw]
    funext ξ
    rw [hu, Real.fourier_smul_convolution_eq hK f.integrable, fourier_heatKernel ht]
    by_cases h : 𝓕 (f : E → F) ξ = 0
    · simp [h]
    · rw [hσ ξ h]
  have hcont : Continuous (heatKernel t ⋆ (f : E → F)) :=
    BddAbove.continuous_convolution_right_of_integrable (lsmul ℝ ℝ)
      ⟨SchwartzMap.seminorm ℝ 0 0 f, fun _ ⟨y, hy⟩ ↦ hy ▸ norm_le_seminorm ℝ f y⟩
      (integrable_heatKernel ht) f.continuous
  have hint : Integrable (heatKernel t ⋆ (f : E → F)) :=
    (integrable_heatKernel ht).integrable_convolution (lsmul ℝ ℝ) f.integrable
  have hFint : Integrable (𝓕 (w : E → F)) := by
    rw [← fourier_coe]
    exact (𝓕 w).integrable
  calc heatKernel t ⋆ (f : E → F) = 𝓕⁻ (𝓕 (heatKernel t ⋆ (f : E → F))) :=
        (hcont.fourierInv_fourier_eq hint (hFu ▸ hFint)).symm
    _ = 𝓕⁻ (𝓕 (w : E → F)) := by rw [hFu]
    _ = w := w.continuous.fourierInv_fourier_eq w.integrable hFint
    _ = _ := hw

/-- For an even cutoff `χ`, the kernel `𝓕⁻ σ` of the frequency-localized heat multiplier is
real-valued. -/
private theorem fourierInv_cutoffHeatSymbol_eq_re {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχe : ∀ ξ, χ (-ξ) = χ ξ) {ν : ℝ} (hν : ν ≠ 0) (t : ℝ) (x : E) :
    (𝓕⁻ (cutoffHeatSymbol hχ hχc hν t) : 𝓢(E, ℂ)) x =
      (((𝓕⁻ (cutoffHeatSymbol hχ hχc hν t) : 𝓢(E, ℂ)) x).re : ℂ) := by
  rw [fourierInv_coe, fourierInv_eq_fourier_neg]
  refine fourier_eq_re_of_map_neg_eq_conj _ (fun v ↦ ?_) (cutoffHeatSymbol hχ hχc hν t).integrable
    (-x)
  simp only [cutoffHeatSymbol_apply, smul_neg, hχe, norm_neg, Complex.conj_ofReal]

/-- For an even cutoff `χ` equal to `1` on the frequencies of `f`, the heat semigroup acts on `f`
as convolution with the real kernel `𝓕⁻ σ` of the frequency-localized heat multiplier. -/
private theorem heatSemigroup_toLp_eq_convolutionLp {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχe : ∀ ξ, χ (-ξ) = χ ξ) {ν : ℝ} (hν : ν ≠ 0) {t : ℝ≥0}
    (ht : t ≠ 0) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (∞ : ℝ≥0∞)) {f : 𝓢(E, F)}
    (hσ : ∀ ξ, 𝓕 (f : E → F) ξ ≠ 0 →
      cutoffHeatSymbol hχ hχc hν t ξ = rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2))) :
    heatSemigroup hp t (f.toLp p) = convolutionLp hp
      (fun x ↦ ((𝓕⁻ (cutoffHeatSymbol hχ hχc hν t) : 𝓢(E, ℂ)) x).re) volume (f.toLp p) := by
  set k : E → ℝ := fun x ↦ ((𝓕⁻ (cutoffHeatSymbol hχ hχc hν t) : 𝓢(E, ℂ)) x).re
  have hconv : heatKernel t ⋆ (f : E → F) = k ⋆ (f : E → F) := by
    rw [heatKernel_convolution_eq_fourierInv_convolution (by positivity) hσ]
    funext x
    simp only [convolution_def, lsmul_apply, k]
    congr 1
    funext y
    rw [fourierInv_cutoffHeatSymbol_eq_re hχ hχc hχe hν t y, Complex.coe_smul,
      Complex.ofReal_re]
  have h₁ := heatSemigroup_ae_eq_convolution hp ht (f.memLp p)
  rw [hconv] at h₁
  exact Lp.ext (h₁.trans (convolutionLp_ae_eq_convolution hp
    (𝓕⁻ (cutoffHeatSymbol hχ hχc hν t)).integrable.re (f.memLp p)).symm)

/-- **The heat flow of a function with frequencies in an annulus.** Let `0 < r` and `R` be real.
There is a constant `C`, depending only on `r`, `R` and `E`, such that for every `1 ≤ p < ∞`,
every frequency scale `ν > 0`, every time `t ≥ 0` and every Schwartz function `f` whose Fourier
transform vanishes outside the annulus `ν r ≤ ‖ξ‖ ≤ ν R`,

`‖e^{tΔ} f‖_p ≤ C exp(-π² r² ν² t / 4) ‖f‖_p`. -/
theorem exists_norm_heatSemigroup_toLp_le_of_support_fourier_subset {r : ℝ} (hr : 0 < r)
    (R : ℝ) :
    ∃ C, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (∞ : ℝ≥0∞)) {ν : ℝ}, 0 < ν →
      ∀ (t : ℝ≥0) (f : 𝓢(E, F)),
      support (𝓕 (f : E → F)) ⊆ closedBall 0 (ν * R) \ ball 0 (ν * r) →
        ‖heatSemigroup hp t (f.toLp p)‖ ≤
          C * rexp (-(π ^ 2 * r ^ 2 / 4 * (ν ^ 2 * t))) * ‖f.toLp p‖ := by
  obtain ⟨χ, hχ, hχc, hχ0, hχe, hχ1⟩ := exists_contDiff_cutoff_annulus (E := E) hr R
  obtain ⟨C₀, hC₀⟩ := exists_integral_norm_fourierInv_mul_exp_le hχ hχc (half_pos hr) hχ0
  refine ⟨max C₀ 1, fun {p} _ hp ν hν t f hf ↦ ?_⟩
  rcases eq_or_ne t 0 with rfl | ht
  · simpa using le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)
  have ht' : (0 : ℝ) < t := by positivity
  set σ := cutoffHeatSymbol hχ hχc hν.ne' t
  set k : E → ℝ := fun x ↦ ((𝓕⁻ σ : 𝓢(E, ℂ)) x).re
  -- `σ` is the heat multiplier on the frequencies of `f`.
  have hσ : ∀ ξ, 𝓕 (f : E → F) ξ ≠ 0 → σ ξ = rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) := by
    intro ξ hξ
    obtain ⟨h₁, h₂⟩ := hf hξ
    rw [mem_closedBall_zero_iff] at h₁
    rw [mem_ball_zero_iff, not_lt] at h₂
    have hn : ‖ν⁻¹ • ξ‖ = ν⁻¹ * ‖ξ‖ := by rw [norm_smul, norm_inv, norm_of_nonneg hν.le]
    rw [cutoffHeatSymbol_apply, hχ1 _ (by rw [hn]; exact (le_inv_mul_iff₀ hν).2 h₂)
      (by rw [hn]; exact (inv_mul_le_iff₀ hν).2 h₁), one_mul]
  have heq := heatSemigroup_toLp_eq_convolutionLp hχ hχc hχe hν.ne' ht hp hσ
  have hkn : ∫ y, ‖k y‖ ≤ C₀ * rexp (-(π ^ 2 * (r / 2) ^ 2 * (ν ^ 2 * t))) := by
    have h := hC₀ ν hν t ht'.le
    rw [← funext (cutoffHeatSymbol_apply hχ hχc hν.ne' t), ← fourierInv_coe] at h
    refine le_of_eq_of_le (integral_congr_ae (.of_forall fun y ↦ ?_)) h
    simp only [k]
    rw [fourierInv_cutoffHeatSymbol_eq_re hχ hχc hχe hν.ne' t y, Complex.ofReal_re,
      Complex.norm_real]
  rw [heq]
  have h₁ : ‖convolutionLp hp k volume (f.toLp p)‖ ≤
      ‖convolutionLp (F := F) hp k volume‖ * ‖f.toLp p‖ :=
    le_opNorm _ _
  have h₂ : ‖convolutionLp (F := F) hp k volume‖ * ‖f.toLp p‖ ≤
      (C₀ * rexp (-(π ^ 2 * (r / 2) ^ 2 * (ν ^ 2 * t)))) * ‖f.toLp p‖ :=
    mul_le_mul_of_nonneg_right ((norm_convolutionLp_le hp k).trans hkn) (norm_nonneg _)
  have h₃ : C₀ * rexp (-(π ^ 2 * (r / 2) ^ 2 * (ν ^ 2 * t))) ≤
      max C₀ 1 * rexp (-(π ^ 2 * r ^ 2 / 4 * (ν ^ 2 * t))) := by
    rw [show π ^ 2 * (r / 2) ^ 2 = π ^ 2 * r ^ 2 / 4 by ring]
    gcongr
    exact le_max_left _ _
  exact h₁.trans (h₂.trans (mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)))

/-- **The heat flow of a Littlewood–Paley block.** Let `ψⱼ` be the inhomogeneous Littlewood–Paley
partition built from the bump function `φ`. There is a constant `C`, depending only on `φ` and
`E`, such that for every `1 ≤ p < ∞`, every `j`, every time `t ≥ 0` and every Schwartz function
`f`, the block `Δ_{j+1} f = 𝓕⁻ (ψ_{j+1} 𝓕 f)`, whose frequencies have size `2^j`, satisfies

`‖e^{tΔ} Δ_{j+1} f‖_p ≤ C exp(-π² φ.rIn² 4^j t / 4) ‖Δ_{j+1} f‖_p`. -/
theorem exists_norm_heatSemigroup_toLp_fourierMultiplierCLM_inhomogeneousLittlewoodPaley_le
    (φ : ContDiffBump (0 : E)) :
    ∃ C, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ (∞ : ℝ≥0∞)) (j : ℕ) (t : ℝ≥0) (f : 𝓢(E, F)),
      ‖heatSemigroup hp t ((fourierMultiplierCLM F
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) f).toLp p)‖ ≤
        C * rexp (-(π ^ 2 * φ.rIn ^ 2 / 4 * (4 ^ j * t))) *
          ‖(fourierMultiplierCLM F
            (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) f).toLp p‖ := by
  obtain ⟨C, hC⟩ := exists_norm_heatSemigroup_toLp_le_of_support_fourier_subset (E := E)
    (F := F) φ.rIn_pos (2 * φ.rOut)
  refine ⟨C, fun {p} _ hp j t f ↦ ?_⟩
  have h4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  refine h4 ▸ hC hp (ν := 2 ^ j) (by positivity) t _ fun ξ hξ ↦ ?_
  -- The Fourier transform of the block is `ψ_{j+1} 𝓕 f`, supported in the annulus of `ψ_{j+1}`.
  rw [← fourier_coe, fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    smulLeftCLM_apply (φ.hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley _),
    mem_support] at hξ
  have hψ : φ.inhomogeneousLittlewoodPaley (j + 1) ξ ≠ 0 := fun h ↦ hξ (by simp [h])
  obtain ⟨h₁, h₂⟩ :=
    φ.tsupport_inhomogeneousLittlewoodPaley_succ_subset j (subset_tsupport _ hψ)
  refine ⟨mem_closedBall_zero_iff.2 (h₂.trans_eq (by ring)), ?_⟩
  rw [mem_ball_zero_iff, not_lt]
  exact h₁

end HeatFlow

end TauCeti
