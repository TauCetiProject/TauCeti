/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Zygmund.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Identification of Hölder–Zygmund and classical Hölder spaces

The companion module `TauCeti.Analysis.Holder.Zygmund.Basic` constructs the forward continuous
inclusions `𝒞^α ⊆ C^{0,α}` and `𝒞^{k+α} ⊆ C_b^{k,α}` for non-integer orders `0 < α < 1`. This file
establishes the converse inclusions `C^{0,α} ⊆ 𝒞^α` and `C_b^{k,α} ⊆ 𝒞^{k+α}` for every `k : ℕ`
and every `α : ℝ≥0` — including the integer endpoints `α = 0` (`C_b^k ⊆ 𝒞^k`) and `α = 1`
(`C_b^{k,1} ⊆ 𝒞^{k+1}`) — and combines both directions into continuous linear equivalences
`𝒞^α ≃L[ℝ] C^{0,α}` and `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}` for `0 < α < 1`.

## The argument

Each dyadic Littlewood–Paley piece `ψ_{j+1}` vanishes at the origin, so its inverse Fourier
transform `κ_{j+1} = 𝓕⁻ ψ_{j+1}` has integral zero
(`ContDiffBump.integral_fourierInv_inhomogeneousLittlewoodPaley_succ`). Writing the block
`Δ_{j+1} f = κ_{j+1} ⋆ f` therefore allows subtracting `f x`:

`(κ_{j+1} ⋆ f) x = ∫ κ_{j+1} y • (f (x - y) - f x) dy`.

For a bounded continuous `f` satisfying a modulus bound
`‖f (x - y) - f x‖ ≤ A ‖y‖^α + B ‖y‖`, taking norms and rescaling the fractional moments of
`κ_{j+1}` (`ContDiffBump.integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ`)
yields

`‖Δ_{j+1} f‖_∞ ≤ A 2^{-α j} M_α + B 2^{-j} M_1`

(`TauCeti.norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le`), where
`M_s = ∫ ‖y‖^s ‖𝓕⁻ ψ₁ y‖ dy`. With `B = 0` this gives `2^{α j} ‖Δ_j f‖_∞ ≤ C ‖f‖_{C^{0,α}}`, so
`C^{0,α} ⊆ 𝒞^α` continuously for every `α : ℝ≥0`.

For higher order `k : ℕ`, integration by parts identifies the distributional iterated directional
derivatives `∂^v f` of a bounded `C^k` function with bounded derivatives of order `< k` with the
pointwise derivatives `x ↦ D^k f(x)(v)` whenever the latter is bounded continuous
(`TauCeti.iteratedLineDerivOp_toLpTop_eq`). Because the
dyadic block `Δ_{j+1} f` has spectrum in the annulus `2^j φ.rIn ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`, the
reverse Bernstein inequality bounds `‖Δ_{j+1} f‖_∞` by `(C / (2^j φ.rIn))^k` times the sum of
`‖Δ_{j+1} (D^k f · (b ∘ i))‖_∞` over basis tuples `i : Fin k → ι`
(`TauCeti.exists_norm_littlewoodPaleyBlock_succ_le_sum_iteratedFDeriv`). Applying the order-zero
cancellation bound to each directional `k`-th derivative yields
`2^{(k + α) j} ‖Δ_j f‖_∞ ≤ C ‖f‖_{C_b^{k,α}}`, giving `C_b^{k,α} ⊆ 𝒞^{k+α}` for every `k : ℕ`
and `α : ℝ≥0`.

For `0 < α < 1`, both maps keep the underlying tempered distribution, and bounded continuous
functions are determined by their tempered distributions, so `toHolderSpace` and `toCkHolderSpace`
are inverse to `HolderSpace.toBesovSpace` and `CkHolderSpace.toBesovSpace`.

## Main declarations

* `ContDiffBump.integral_fourierInv_inhomogeneousLittlewoodPaley_succ`: the dyadic kernels
  `𝓕⁻ ψ_{j+1}` have integral zero.
* `ContDiffBump.integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ`: the
  `s`-th moment of `𝓕⁻ ψ_{j+1}` scales by `2^{-s j}`.
* `TauCeti.norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le`: kernel cancellation bound for the
  dyadic blocks of a bounded continuous function with an `A ‖y‖^α + B ‖y‖` increment estimate.
* `TauCeti.iteratedLineDerivOp_toLpTop_eq`: distributional iterated directional derivatives of a
  bounded `C^k` function with bounded derivatives of order `< k`.
* `TauCeti.exists_norm_littlewoodPaleyBlock_succ_le_sum_iteratedFDeriv`: reverse Bernstein bound
  on dyadic blocks of a bounded `C^k` function in terms of the blocks of its `k`-th directional
  derivatives.
* `TauCeti.HolderSpace.memBesov` and `TauCeti.HolderSpace.toBesovSpace`: the continuous inclusion
  `C^{0,α} ⊆ 𝒞^α` for every `α : ℝ≥0`.
* `TauCeti.BesovSpace.holderSpaceEquiv`: the continuous linear equivalence `𝒞^α ≃L[ℝ] C^{0,α}`
  for `0 < α < 1`, with unbundled characterisation
  `TemperedDistribution.memBesov_iff_exists_holderSpace`.
* `TauCeti.CkHolderSpace.memBesov` and `TauCeti.CkHolderSpace.toBesovSpace`: the continuous
  inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}` for every `k : ℕ` and `α : ℝ≥0`.
* `TauCeti.BesovSpace.ckHolderSpaceEquiv`: the continuous linear equivalence
  `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}` for `0 < α < 1`, with unbundled characterisation
  `TemperedDistribution.memBesov_iff_exists_ckHolderSpace`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Theorem 2.36 and
  Section 2.7.
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, Section 2.5.7.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution BoundedContinuousFunction Module
open scoped ENNReal NNReal SchwartzMap Convolution LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-! ### Kernel cancellation and fractional moments -/

namespace ContDiffBump

variable (φ : ContDiffBump (0 : E))

/-- **Cancellation of the dyadic kernels.** Every dyadic Littlewood–Paley piece `ψ_{j+1}` vanishes
at the origin, so its inverse Fourier transform `𝓕⁻ ψ_{j+1}` has integral zero. -/
theorem integral_fourierInv_inhomogeneousLittlewoodPaley_succ (j : ℕ) :
    ∫ y, 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) y = 0 := by
  set σ : 𝓢(E, ℂ) := φ.inhomogeneousLittlewoodPaleySchwartz (j + 1)
  have hσ : (σ : E → ℂ) = fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ) :=
    φ.coe_inhomogeneousLittlewoodPaleySchwartz (j + 1)
  have hF : (𝓕 (𝓕⁻ σ : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) 0 = ∫ y, (𝓕⁻ σ : 𝓢(E, ℂ)) y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp
  rw [← hσ, ← SchwartzMap.fourierInv_coe, ← hF, FourierTransform.fourier_fourierInv_eq]
  have h0 : σ 0 = (φ.inhomogeneousLittlewoodPaley (j + 1) 0 : ℂ) := congrFun hσ 0
  rw [h0, φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le (by simp [φ.rIn_pos.le]),
    Complex.ofReal_zero]

/-- **Scaling of fractional moments of the dyadic kernels.** Since `𝓕⁻ ψ_{j+1}` is the
`L¹`-normalised dilate `2^{jn} 𝓕⁻ ψ₁ (2^j ·)` in dimension `n`, its `s`-th moment
`∫ ‖y‖ ^ s ‖𝓕⁻ ψ_{j+1} y‖` is `2^{-s j}` times that of `𝓕⁻ ψ₁`. -/
theorem integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ (s : ℝ) (j : ℕ) :
    ∫ y, ‖y‖ ^ s * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) y‖ =
      ((2 : ℝ) ^ (s * j))⁻¹ *
        ∫ y, ‖y‖ ^ s * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖ := by
  set c : ℝ := ((2 : ℝ) ^ j)⁻¹
  set K₁ : E → ℂ := 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ))
  have hc0 : 0 < c := by positivity
  have hc' : |c ^ finrank ℝ E| ≠ 0 := abs_ne_zero.2 (pow_ne_zero _ hc0.ne')
  have hcs : c ^ s * (c ^ s)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have h (y : E) :
      ‖y‖ ^ s * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) y‖ =
        (|c ^ finrank ℝ E|⁻¹ * c ^ s) * (‖c⁻¹ • y‖ ^ s * ‖K₁ (c⁻¹ • y)‖) := by
    simp_rw [φ.inhomogeneousLittlewoodPaley_succ_apply_eq_one_apply j]
    rw [TauCeti.fourierInv_comp_smul (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) c y,
      norm_smul, norm_smul, norm_inv, norm_inv, Real.norm_of_nonneg (abs_nonneg _),
      Real.norm_of_nonneg hc0.le, Real.mul_rpow (inv_nonneg.2 hc0.le) (norm_nonneg y),
      Real.inv_rpow hc0.le]
    calc ‖y‖ ^ s * (|c ^ finrank ℝ E|⁻¹ * ‖K₁ (c⁻¹ • y)‖)
        = |c ^ finrank ℝ E|⁻¹ * (c ^ s * (c ^ s)⁻¹) * (‖y‖ ^ s * ‖K₁ (c⁻¹ • y)‖) := by
          rw [hcs, mul_one]
          ring
      _ = (|c ^ finrank ℝ E|⁻¹ * c ^ s) * ((c ^ s)⁻¹ * ‖y‖ ^ s * ‖K₁ (c⁻¹ • y)‖) := by ring
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume (fun y ↦ ‖y‖ ^ s * ‖K₁ y‖),
    smul_eq_mul, ← mul_assoc, mul_right_comm |c ^ finrank ℝ E|⁻¹, inv_mul_cancel₀ hc', one_mul]
  congr 1
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast (2 : ℝ) j,
    ← Real.rpow_mul zero_le_two, mul_comm]

end ContDiffBump

namespace TauCeti

section KernelCancellation

/-- For any Schwartz function `κ` and `α : ℝ≥0`, `y ↦ ‖y‖ ^ (α : ℝ) * ‖κ y‖` is integrable. -/
private theorem integrable_norm_rpow_mul_norm_schwartz (κ : 𝓢(E, ℂ)) (α : ℝ≥0) :
    Integrable (fun y ↦ ‖y‖ ^ (α : ℝ) * ‖κ y‖) volume := by
  set N : ℕ := ⌈(α : ℝ)⌉₊
  have hdom : Integrable (fun y : E ↦ ‖κ y‖ + ‖y‖ ^ N * ‖κ y‖) volume :=
    (κ.integrable (μ := volume)).norm.add (κ.integrable_pow_mul volume N)
  refine hdom.mono'
    (((continuous_norm.rpow_const fun _ ↦ Or.inr α.coe_nonneg).mul
      κ.continuous.norm).aestronglyMeasurable) (Filter.Eventually.of_forall fun y ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have hrpow : ‖y‖ ^ (α : ℝ) ≤ 1 + ‖y‖ ^ N := by
    rcases le_or_gt ‖y‖ 1 with hy | hy
    · exact (Real.rpow_le_one (norm_nonneg y) hy α.coe_nonneg).trans (le_add_of_nonneg_right
        (by positivity))
    · calc ‖y‖ ^ (α : ℝ) ≤ ‖y‖ ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hy.le (Nat.le_ceil _)
        _ = ‖y‖ ^ N := Real.rpow_natCast _ _
        _ ≤ 1 + ‖y‖ ^ N := le_add_of_nonneg_left zero_le_one
  calc ‖y‖ ^ (α : ℝ) * ‖κ y‖ ≤ (1 + ‖y‖ ^ N) * ‖κ y‖ := by gcongr
    _ = ‖κ y‖ + ‖y‖ ^ N * ‖κ y‖ := by ring

/-- **Kernel cancellation estimate for dyadic blocks.** If a bounded continuous function `f`
satisfies `‖f (x - y) - f x‖ ≤ A ‖y‖^α + B ‖y‖` for all `x, y`, then its dyadic block `Δ_{j+1} f`
has `L^∞` norm bounded by `A 2^{-α j} M_α + B 2^{-j} M_1`, where
`M_s = ∫ ‖y‖^s ‖𝓕⁻ ψ₁ y‖ dy`. -/
theorem norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le (φ : ContDiffBump (0 : E)) {α : ℝ≥0}
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {f : E →ᵇ F}
    (hf : ∀ x y, ‖f (x - y) - f x‖ ≤ A * ‖y‖ ^ (α : ℝ) + B * ‖y‖)
    {j : ℕ} {v : Lp F ∞ (volume : Measure E)}
    (hv : littlewoodPaleyBlock F φ (j + 1) (toLpTop volume ℂ f : 𝓢'(E, F)) = v) :
    ‖v‖ ≤ A * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ *
        (∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖) +
      B * ((2 : ℝ) ^ j)⁻¹ *
        (∫ y, ‖y‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖) := by
  set κ : 𝓢(E, ℂ) := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz (j + 1))
  have hκ : (κ : E → ℂ) = 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley (j + 1) ξ : ℂ)) := by
    rw [SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  have hκ0 : ∫ y, κ y = 0 := by
    rw [hκ]
    exact φ.integral_fourierInv_inhomogeneousLittlewoodPaley_succ j
  have hMα : Integrable (fun y ↦ ‖y‖ ^ (α : ℝ) * ‖κ y‖) volume :=
    integrable_norm_rpow_mul_norm_schwartz κ α
  have hM1 : Integrable (fun y ↦ ‖y‖ * ‖κ y‖) volume := by
    simpa only [NNReal.coe_one, Real.rpow_one] using integrable_norm_rpow_mul_norm_schwartz κ 1
  -- `v` agrees almost everywhere with the convolution `κ ⋆ f`.
  have hae : (v : E → F) =ᵐ[volume] (κ : E → ℂ) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (f : E → F) := by
    refine (ae_eq_convolution_of_littlewoodPaleyBlock_eq φ (j + 1) hv).trans ?_
    filter_upwards with x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, hκ]
    refine integral_congr_ae ?_
    have hsub := (Measure.measurePreserving_sub_left (volume : Measure E) x).quasiMeasurePreserving
      |>.ae_eq_comp (coeFn_toLpTop (𝕜 := ℂ) (volume : Measure E) f)
    filter_upwards [hsub] with y hy
    rw [Function.comp_apply, Function.comp_apply] at hy
    rw [hy]
  -- Subtract `f x` using `∫ κ = 0` and apply the increment bound pointwise.
  have hpt (x : E) :
      ‖((κ : E → ℂ) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (f : E → F)) x‖ ≤
        A * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ *
            (∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖) +
          B * ((2 : ℝ) ^ j)⁻¹ *
            (∫ y, ‖y‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖) := by
    have hint1 : Integrable (fun y ↦ κ y • f (x - y)) volume :=
      ((κ.integrable (μ := volume)).norm.mul_const ‖f‖).mono'
        ((κ.continuous.smul (f.continuous.comp (continuous_const.sub continuous_id))
          ).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y ↦ by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x - y)) (norm_nonneg _))
    have hint2 : Integrable (fun y ↦ κ y • f x) volume :=
      (κ.integrable (μ := volume)).smul_const (f x)
    have hsub_eq :
        ((κ : E → ℂ) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] (f : E → F)) x =
          ∫ y, κ y • (f (x - y) - f x) := by
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_sub]
      rw [integral_sub hint1 hint2, integral_smul_const, hκ0, zero_smul, sub_zero]
    rw [hsub_eq]
    have hbound_int : Integrable (fun y ↦ A * (‖y‖ ^ (α : ℝ) * ‖κ y‖) + B * (‖y‖ * ‖κ y‖)) volume :=
      (hMα.const_mul A).add (hM1.const_mul B)
    have hM1_eq : ∫ y, ‖y‖ * ‖κ y‖ =
        ((2 : ℝ) ^ j)⁻¹ *
          ∫ y, ‖y‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖ := by
      rw [hκ]
      simpa only [pow_one] using
        φ.integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ 1 j
    have hMα_eq : ∫ y, ‖y‖ ^ (α : ℝ) * ‖κ y‖ =
        ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ *
          ∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖ := by
      rw [hκ]
      exact φ.integral_norm_rpow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_succ (α : ℝ) j
    calc ‖∫ y, κ y • (f (x - y) - f x)‖
        ≤ ∫ y, ‖κ y • (f (x - y) - f x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (A * (‖y‖ ^ (α : ℝ) * ‖κ y‖) + B * (‖y‖ * ‖κ y‖)) := by
          refine integral_mono (hint1.sub hint2 |>.norm.congr <| Filter.Eventually.of_forall
            fun y ↦ by simp only [Pi.sub_apply, smul_sub]) hbound_int fun y ↦ ?_
          rw [norm_smul]
          calc ‖κ y‖ * ‖f (x - y) - f x‖
              ≤ ‖κ y‖ * (A * ‖y‖ ^ (α : ℝ) + B * ‖y‖) := by gcongr; exact hf x y
            _ = A * (‖y‖ ^ (α : ℝ) * ‖κ y‖) + B * (‖y‖ * ‖κ y‖) := by ring
      _ = A * (∫ y, ‖y‖ ^ (α : ℝ) * ‖κ y‖) + B * (∫ y, ‖y‖ * ‖κ y‖) := by
          rw [integral_add (hMα.const_mul A) (hM1.const_mul B), integral_const_mul,
            integral_const_mul]
      _ = A * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ *
            (∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖) +
          B * ((2 : ℝ) ^ j)⁻¹ *
            (∫ y, ‖y‖ * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖) := by
          rw [hMα_eq, hM1_eq]
          ring
  refine Lp.norm_top_le_of_ae_bound (by
    refine add_nonneg (mul_nonneg (mul_nonneg hA (by positivity))
      (integral_nonneg fun _ ↦ by positivity))
      (mul_nonneg (mul_nonneg hB (by positivity)) (integral_nonneg fun _ ↦ by positivity))) ?_
  filter_upwards [hae] with x hx
  rw [hx]
  exact hpt x

end KernelCancellation

/-! ### Order-zero inclusion `C^{0,α} ⊆ 𝒞^α` and equivalence `𝒞^α ≃L[ℝ] C^{0,α}` -/

namespace HolderSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- Uniform weighted block bound for `C^{0,α}` functions, valid for every `α : ℝ≥0`. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : HolderSpace α E F) (j : ℕ),
      ∃ v : Lp F ∞ (volume : Measure E),
        littlewoodPaleyBlock F φ j (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) =
          v ∧ 2 ^ ((α : ℝ) * j) * ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set Mα : ℝ :=
    ∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  set C : ℝ := max (max C₀ 0) (2 ^ (α : ℝ) * Mα)
  refine ⟨C, (le_max_right C₀ 0).trans (le_max_left _ _), fun f j ↦ ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC₀ j (toLpTop volume ℂ f.toBoundedContinuousFunction)
  refine ⟨v, hv, ?_⟩
  rcases j with _ | j
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
    calc ‖v‖ ≤ C₀ * ‖toLpTop volume ℂ f.toBoundedContinuousFunction‖ := hvC
      _ ≤ max C₀ 0 * ‖f‖ := mul_le_mul (le_max_left _ _)
            ((norm_toLpTop_le volume _).trans f.norm_toBoundedContinuousFunction_le)
            (norm_nonneg _) (le_max_right _ _)
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)
  · have hinc : ∀ x y, ‖f.toBoundedContinuousFunction (x - y) -
        f.toBoundedContinuousFunction x‖ ≤ ‖f‖ * ‖y‖ ^ (α : ℝ) + 0 * ‖y‖ := fun x y ↦ by
      rw [zero_mul, add_zero, toBoundedContinuousFunction_apply, toBoundedContinuousFunction_apply,
        ← dist_eq_norm]
      have h := f.holderWith_nnnorm.dist_le (x - y) x
      rwa [coe_nnNorm, dist_eq_norm (x - y) x, sub_sub_cancel_left, norm_neg] at h
    have hv_bound := norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le φ (norm_nonneg f) le_rfl
      hinc hv
    rw [zero_mul, zero_mul, add_zero] at hv_bound
    have hpow : (2 : ℝ) ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) =
        2 ^ (α : ℝ) * 2 ^ ((α : ℝ) * j) := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.rpow_add two_pos, mul_comm]
    calc 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * ‖v‖
        ≤ 2 ^ ((α : ℝ) * ((j + 1 : ℕ) : ℝ)) * (‖f‖ * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ * Mα) := by
          gcongr
      _ = (2 ^ (α : ℝ) * Mα) * ‖f‖ := by
          rw [hpow]
          have hpos : (2 : ℝ) ^ ((α : ℝ) * j) ≠ 0 := by positivity
          field_simp
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg f)

/-- **Every bounded `α`-Hölder function lies in `𝒞^α = B^α_{∞,∞}`**, for every `α : ℝ≥0`. -/
theorem memBesov (f : HolderSpace α E F) :
    (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)).MemBesov φ α ∞ ∞ := by
  obtain ⟨C, -, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (α := α) φ
  choose g hg hgb using h f
  refine memBesov_iff.2 ⟨g, hg, memℓp_infty ⟨C * ‖f‖, ?_⟩⟩
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hgb j

/-- **The inclusion `C^{0,α} ⊆ 𝒞^α`** for every `α : ℝ≥0`, as a continuous linear map from the
bounded `α`-Hölder space to the Hölder–Zygmund space `B^α_{∞,∞}` built from `φ`. -/
def toBesovSpace : HolderSpace α E F →L[ℝ] BesovSpace F φ α ∞ ∞ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun f := (f.memBesov φ).toBesovSpace
      map_add' f g := BesovSpace.ext <| by
        simp [HolderSpace.toBoundedContinuousFunction_add, map_add, Lp.toTemperedDistribution_add]
      map_smul' c f := BesovSpace.ext <| by
        simp only [RingHom.id_apply, MemBesov.toDistr_toBesovSpace,
          HolderSpace.toBoundedContinuousFunction_smul]
        rw [← Complex.coe_smul c f.toBoundedContinuousFunction, map_smul,
          Lp.toTemperedDistribution_smul, ← Complex.coe_smul c ((f.memBesov φ).toBesovSpace),
          BesovSpace.toDistr_smul, MemBesov.toDistr_toBesovSpace] } <| by
    obtain ⟨C, -, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (α := α) φ
    refine ⟨C, fun f ↦ ?_⟩
    set v := (f.memBesov φ).toBesovSpace
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [BesovSpace.norm_eq_ciSup]
    refine ciSup_le fun j ↦ ?_
    obtain ⟨g, hg, hgf⟩ := hC f j
    have hvg : v.block j = g := Lp.toTemperedDistribution_injective <| by
      simp only [BesovSpace.coe_block, ← hg, v, MemBesov.toDistr_toBesovSpace]
    rw [hvg]
    exact hgf

/-- The inclusion `HolderSpace.toBesovSpace` keeps the underlying tempered distribution. -/
@[simp]
theorem toDistr_toBesovSpace (f : HolderSpace α E F) :
    (toBesovSpace φ f).toDistr =
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) := by
  simp [toBesovSpace]

end HolderSpace

namespace BesovSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- `HolderSpace.toBesovSpace` is left inverse to `BesovSpace.toHolderSpace`. -/
@[simp]
theorem toBesovSpace_toHolderSpace (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    HolderSpace.toBesovSpace φ (toHolderSpace F φ hα0 hα1 u) = u :=
  ext <| by simp

/-- `BesovSpace.toHolderSpace` is left inverse to `HolderSpace.toBesovSpace`. -/
@[simp]
theorem toHolderSpace_toBesovSpace (hα0 : 0 < α) (hα1 : α < 1) (f : HolderSpace α E F) :
    toHolderSpace F φ hα0 hα1 (HolderSpace.toBesovSpace φ f) = f :=
  (toHolderSpace_eq_iff φ hα0 hα1).2 (by simp)

variable (F) in
/-- **Identification `𝒞^α ≃L[ℝ] C^{0,α}`** for `0 < α < 1`: the Hölder–Zygmund space `B^α_{∞,∞}`
is continuously linearly equivalent to the bounded `α`-Hölder space `C^{0,α}`. -/
def holderSpaceEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ α ∞ ∞ ≃L[ℝ] HolderSpace α E F :=
  ContinuousLinearEquiv.equivOfInverse
    (toHolderSpace F φ hα0 hα1) (HolderSpace.toBesovSpace φ)
    (toBesovSpace_toHolderSpace φ hα0 hα1) (toHolderSpace_toBesovSpace φ hα0 hα1)

/-- Forward evaluation of `BesovSpace.holderSpaceEquiv` is `BesovSpace.toHolderSpace`. -/
@[simp]
theorem holderSpaceEquiv_apply (hα0 : 0 < α) (hα1 : α < 1) (u : BesovSpace F φ α ∞ ∞) :
    holderSpaceEquiv F φ hα0 hα1 u = toHolderSpace F φ hα0 hα1 u :=
  (rfl)

/-- Inverse evaluation of `BesovSpace.holderSpaceEquiv` is `HolderSpace.toBesovSpace`. -/
@[simp]
theorem holderSpaceEquiv_symm_apply (hα0 : 0 < α) (hα1 : α < 1) (f : HolderSpace α E F) :
    (holderSpaceEquiv F φ hα0 hα1).symm f = HolderSpace.toBesovSpace φ f :=
  (rfl)

end BesovSpace

end TauCeti

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- **Unbundled identification `𝒞^α = C^{0,α}`** for `0 < α < 1`: a tempered distribution lies in
`B^α_{∞,∞}` exactly when it is the tempered distribution of a bounded `α`-Hölder function. -/
theorem memBesov_iff_exists_holderSpace (hα0 : 0 < α) (hα1 : α < 1) {u : 𝓢'(E, F)} :
    u.MemBesov φ α ∞ ∞ ↔
      ∃ f : TauCeti.HolderSpace α E F,
        (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u :=
  ⟨fun hu ↦ ⟨TauCeti.BesovSpace.toHolderSpace F φ hα0 hα1 hu.toBesovSpace, by simp⟩,
    fun ⟨f, hf⟩ ↦ hf ▸ f.memBesov φ⟩

end TemperedDistribution

/-! ### Distributional derivatives of bounded `C^k` functions -/

namespace TauCeti

section DistributionalDeriv

/-- One-step integration by parts: if `f` and `g` are bounded continuous with `f` differentiable
and `g x = fderiv ℝ f x v`, then `∂_v f = g` in `𝓢'(E, F)`. -/
private theorem lineDerivOp_toLpTop_eq {f g : E →ᵇ F} (hf : Differentiable ℝ f) (v : E)
    (hg : ∀ x, g x = fderiv ℝ f x v) :
    ∂_{v} (toLpTop volume ℂ f : 𝓢'(E, F)) = (toLpTop volume ℂ g : 𝓢'(E, F)) := by
  ext ψ
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have h1 : ∫ x, (-∂_{v} ψ) x • (toLpTop volume ℂ f : E → F) x =
      -∫ x, fderiv ℝ (ψ : E → ℂ) x v • f x := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toLpTop (𝕜 := ℂ) (volume : Measure E) f] with x hx
    simp only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, neg_smul, hx]
  have h2 : ∫ x, ψ x • (toLpTop volume ℂ g : E → F) x = ∫ x, ψ x • fderiv ℝ f x v := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toLpTop (𝕜 := ℂ) (volume : Measure E) g] with x hx
    rw [hx, hg x]
  rw [h1, h2]
  have hf'g : Integrable (fun x ↦ fderiv ℝ (ψ : E → ℂ) x v • f x) volume := by
    refine (((∂_{v} ψ).integrable (μ := volume)).norm.mul_const ‖f‖).mono'
      (((∂_{v} ψ).continuous.congr (fun x ↦ SchwartzMap.lineDerivOp_apply_eq_fderiv v ψ x)).smul
        f.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [norm_smul, ← SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)
  have hfg' : Integrable (fun x ↦ ψ x • fderiv ℝ f x v) volume := by
    refine ((ψ.integrable (μ := volume)).norm.mul_const ‖g‖).mono'
      (ψ.continuous.smul (g.continuous.congr hg)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [norm_smul, ← hg x]
    exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm x) (norm_nonneg _)
  have hfg : Integrable (fun x ↦ ψ x • f x) volume :=
    ((ψ.integrable (μ := volume)).norm.mul_const ‖f‖).mono'
      (ψ.continuous.smul f.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _))
  exact (integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hf'g hfg' hfg
    (fun x _ ↦ ψ.differentiableAt) (fun x _ ↦ hf x)).symm

/-- **Distributional iterated directional derivatives of bounded `C^k` functions.** If `f` is
bounded `C^k` with bounded derivatives of order `< k` and `g` is bounded continuous with
`g x = iteratedFDeriv ℝ k f x v`, then `∂^v f = g` in `𝓢'(E, F)`. -/
theorem iteratedLineDerivOp_toLpTop_eq {k : ℕ} {f g : E →ᵇ F} (hf : ContDiff ℝ k f)
    (hbdd : ∀ i < k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C) (v : Fin k → E)
    (hg : ∀ x, g x = iteratedFDeriv ℝ k f x v) :
    ∂^{v} (toLpTop volume ℂ f : 𝓢'(E, F)) = (toLpTop volume ℂ g : 𝓢'(E, F)) := by
  induction k generalizing g with
  | zero =>
    have hfg : f = g := by
      ext x
      simpa only [iteratedFDeriv_zero_apply] using (hg x).symm
    simp [hfg]
  | succ k ih =>
    obtain ⟨C, hC⟩ := hbdd k (Nat.lt_succ_self k)
    have hcont : Continuous fun x ↦ iteratedFDeriv ℝ k f x (Fin.tail v) :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (Fin.tail v)).continuous).comp
        (hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ k))
    have hbd : ∀ x, ‖iteratedFDeriv ℝ k f x (Fin.tail v)‖ ≤ C * ∏ i, ‖Fin.tail v i‖ := fun x ↦
      (ContinuousMultilinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC x) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
    set g' : E →ᵇ F := ofNormedAddCommGroup (fun x ↦ iteratedFDeriv ℝ k f x (Fin.tail v))
      hcont (C * ∏ i, ‖Fin.tail v i‖) hbd
    have hih : ∂^{Fin.tail v} (toLpTop volume ℂ f : 𝓢'(E, F)) =
        (toLpTop volume ℂ g' : 𝓢'(E, F)) :=
      ih (hf.of_le (by exact_mod_cast Nat.le_succ k))
        (fun i hi ↦ hbdd i (hi.trans (Nat.lt_succ_self k))) (Fin.tail v) fun x ↦ rfl
    have hdiff : ∀ x, HasFDerivAt (g' : E → F)
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (Fin.tail v)).comp
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
            (iteratedFDeriv ℝ (k + 1) f x))) x := fun x ↦ by
      have hF : HasFDerivAt (iteratedFDeriv ℝ k f)
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
            (iteratedFDeriv ℝ (k + 1) f x)) x := by
        have h := (hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k) x
          ).hasFDerivAt
        rwa [fderiv_iteratedFDeriv] at h
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (Fin.tail v)).hasFDerivAt.comp
        x hF
    rw [LineDeriv.iteratedLineDerivOp_succ_left, hih]
    refine lineDerivOp_toLpTop_eq (fun x ↦ (hdiff x).differentiableAt) (v 0) fun x ↦ ?_
    rw [hg x, (hdiff x).fderiv]
    simp [Fin.cons_self_tail]

/-- **Reverse Bernstein bound on dyadic blocks of bounded `C^k` functions.** Given an orthonormal
basis `b` of `E`, there is `C ≥ 0` depending only on `φ` and `b` such that for every `k : ℕ`,
every bounded `C^k` function `f` with bounded derivatives of order `< k` whose directional `k`-th
derivatives `g i x = D^k f(x)(b ∘ i)` are bounded continuous, and every `j : ℕ`,
`‖Δ_{j+1} f‖_∞ ≤ (C / (2^j φ.rIn))^k ∑ᵢ ‖Δ_{j+1} (g i)‖_∞`. -/
theorem exists_norm_littlewoodPaleyBlock_succ_le_sum_iteratedFDeriv (φ : ContDiffBump (0 : E))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (f : E →ᵇ F) (g : (Fin k → ι) → E →ᵇ F) (j : ℕ)
      (v : Lp F ∞ (volume : Measure E)) (w : (Fin k → ι) → Lp F ∞ (volume : Measure E)),
      ContDiff ℝ k f → (∀ m < k, ∃ M, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ M) →
      (∀ i x, g i x = iteratedFDeriv ℝ k f x (b ∘ i)) →
      littlewoodPaleyBlock F φ (j + 1) (toLpTop volume ℂ f : 𝓢'(E, F)) = v →
      (∀ i, littlewoodPaleyBlock F φ (j + 1) (toLpTop volume ℂ (g i) : 𝓢'(E, F)) = w i) →
      ‖v‖ ≤ (C / (2 ^ j * φ.rIn)) ^ k * ∑ i, ‖w i‖ := by
  obtain ⟨C, hC0, hB⟩ := b.exists_norm_le_div_pow_mul_sum_norm_of_iteratedLineDerivOp_eq
    (F := F) (2 * φ.rOut / φ.rIn)
  refine ⟨C, hC0, fun k f g j v w hf hbdd hg hv hw ↦ ?_⟩
  have hR : 0 < (2 : ℝ) ^ j * φ.rIn := mul_pos (by positivity) φ.rIn_pos
  have hBR : 2 * φ.rOut / φ.rIn * ((2 : ℝ) ^ j * φ.rIn) = (2 : ℝ) ^ (j + 1) * φ.rOut := by
    have hIn : φ.rIn ≠ 0 := φ.rIn_pos.ne'
    rw [pow_succ]
    field_simp
  have hspec : Distribution.IsVanishingOn (𝓕 (v : 𝓢'(E, F)) : 𝓢'(E, F))
      (Metric.ball 0 ((2 : ℝ) ^ j * φ.rIn) ∪
        (Metric.closedBall 0 (2 * φ.rOut / φ.rIn * ((2 : ℝ) ^ j * φ.rIn)))ᶜ) := by
    rw [← hv, hBR]
    refine (isVanishingOn_fourier_littlewoodPaleyBlock_succ φ j _).mono fun ξ hξ ↦ ?_
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_sdiff, not_and_or, not_not] at hξ ⊢
    exact hξ.symm
  refine hB k hR v w hspec fun i ↦ ?_
  rw [← hv, ← littlewoodPaleyBlock_iteratedLineDerivOp,
    iteratedLineDerivOp_toLpTop_eq hf hbdd (⇑b ∘ i) (hg i), hw i]

end DistributionalDeriv

/-! ### Higher-order inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}` and equivalence `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}` -/

namespace CkHolderSpace

variable (φ : ContDiffBump (0 : E)) {k : ℕ} {α : ℝ≥0}

/-- Uniform weighted block bound for `C_b^{k,α}` functions, valid for every `k : ℕ` and
`α : ℝ≥0`. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : CkHolderSpace k α E F) (j : ℕ),
      ∃ v : Lp F ∞ (volume : Measure E),
        littlewoodPaleyBlock F φ j (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) =
          v ∧ 2 ^ (((k : ℝ) + α) * j) * ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Cr, hCr0, hrev⟩ := exists_norm_littlewoodPaleyBlock_succ_le_sum_iteratedFDeriv
    (F := F) φ b
  set Mα : ℝ :=
    ∫ y, ‖y‖ ^ (α : ℝ) * ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley 1 ξ : ℂ)) y‖
  have hIn : 0 < φ.rIn := φ.rIn_pos
  set K : ℝ := (2 * Cr / φ.rIn) ^ k * (finrank ℝ E : ℝ) ^ k * (2 ^ (α : ℝ) * Mα)
  set C : ℝ := max (max C₀ 0) K
  refine ⟨C, (le_max_right C₀ 0).trans (le_max_left _ _), fun f j ↦ ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC₀ j (toLpTop volume ℂ f.toBoundedContinuousFunction)
  refine ⟨v, hv, ?_⟩
  rcases j with _ | j
  · simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
    calc ‖v‖ ≤ C₀ * ‖toLpTop volume ℂ f.toBoundedContinuousFunction‖ := hvC
      _ ≤ max C₀ 0 * ‖f‖ := mul_le_mul (le_max_left _ _)
            ((norm_toLpTop_le volume _).trans f.norm_toBoundedContinuousFunction_le)
            (norm_nonneg _) (le_max_right _ _)
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg f)
  · -- Each directional `k`-th derivative `g i x = D^k f(x)(b ∘ i)` is bounded continuous and
    -- `α`-Hölder with constant `‖f‖`.
    have hnorm_b : ∀ (i : Fin k → Fin (finrank ℝ E)), ∏ r, ‖b (i r)‖ = 1 := fun i ↦
      Finset.prod_eq_one fun r _ ↦ b.orthonormal.1 (i r)
    set g : (Fin k → Fin (finrank ℝ E)) → E →ᵇ F := fun i ↦
      ofNormedAddCommGroup (fun x ↦ _root_.iteratedFDeriv ℝ k f x (⇑b ∘ i))
        (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F (⇑b ∘ i)).continuous).comp
          (f.contDiff.continuous_iteratedFDeriv le_rfl))
        ‖f‖ fun x ↦ by
          refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
          rw [Function.comp_def, hnorm_b i, mul_one]
          exact f.norm_iteratedFDeriv_apply_le le_rfl x
    choose w hw _ using fun i ↦ hC₀ (j + 1) (toLpTop volume ℂ (g i))
    have hrev_j : ‖v‖ ≤ (Cr / (2 ^ j * φ.rIn)) ^ k * ∑ i, ‖w i‖ :=
      hrev k f.toBoundedContinuousFunction g j v w
        (by simpa only [coe_toBoundedContinuousFunction] using f.contDiff)
        (fun m hm ↦ ⟨‖f‖, fun x ↦ by
          simpa only [coe_toBoundedContinuousFunction] using
            f.norm_iteratedFDeriv_apply_le hm.le x⟩)
        (fun i x ↦ by rw [coe_toBoundedContinuousFunction]; rfl) hv hw
    have hw_le (i : Fin k → Fin (finrank ℝ E)) :
        ‖w i‖ ≤ ‖f‖ * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ * Mα := by
      have hinc : ∀ x y, ‖g i (x - y) - g i x‖ ≤ ‖f‖ * ‖y‖ ^ (α : ℝ) + 0 * ‖y‖ := fun x y ↦ by
        rw [zero_mul, add_zero]
        have heval : g i (x - y) - g i x =
            (_root_.iteratedFDeriv ℝ k f (x - y) - _root_.iteratedFDeriv ℝ k f x) (⇑b ∘ i) := rfl
        rw [heval]
        calc ‖(_root_.iteratedFDeriv ℝ k f (x - y) - _root_.iteratedFDeriv ℝ k f x) (⇑b ∘ i)‖
            ≤ ‖_root_.iteratedFDeriv ℝ k f (x - y) - _root_.iteratedFDeriv ℝ k f x‖ *
                ∏ r, ‖b (i r)‖ := ContinuousMultilinearMap.le_opNorm _ _
          _ = dist (_root_.iteratedFDeriv ℝ k f (x - y)) (_root_.iteratedFDeriv ℝ k f x) := by
                rw [hnorm_b i, mul_one, dist_eq_norm]
          _ ≤ nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) * dist (x - y) x ^ (α : ℝ) :=
                f.memHolder_iteratedFDeriv.holderWith.dist_le (x - y) x
          _ ≤ ‖f‖ * ‖y‖ ^ (α : ℝ) := by
                rw [dist_eq_norm (x - y) x, sub_sub_cancel_left, norm_neg]
                exact mul_le_mul_of_nonneg_right f.nnHolderNorm_iteratedFDeriv_le (by positivity)
      have h := norm_littlewoodPaleyBlock_succ_le_of_norm_sub_le φ (norm_nonneg f) le_rfl hinc
        (hw i)
      rwa [zero_mul, zero_mul, add_zero] at h
    have hsum : ∑ i : Fin k → Fin (finrank ℝ E), ‖w i‖ ≤
        (finrank ℝ E : ℝ) ^ k * (‖f‖ * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ * Mα) := by
      refine (Finset.sum_le_sum fun i _ ↦ hw_le i).trans ?_
      simp [Finset.card_univ]
    have hpow : (2 : ℝ) ^ (((k : ℝ) + α) * ((j + 1 : ℕ) : ℝ)) =
        (2 ^ (j + 1)) ^ k * (2 ^ (α : ℝ) * 2 ^ ((α : ℝ) * j)) := by
      rw [add_mul, Real.rpow_add two_pos, mul_comm (k : ℝ), Real.rpow_mul_natCast zero_le_two,
        Real.rpow_natCast, Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.rpow_add two_pos,
        mul_comm (2 ^ ((α : ℝ) * j))]
    calc 2 ^ (((k : ℝ) + α) * ((j + 1 : ℕ) : ℝ)) * ‖v‖
        ≤ 2 ^ (((k : ℝ) + α) * ((j + 1 : ℕ) : ℝ)) *
            ((Cr / (2 ^ j * φ.rIn)) ^ k *
              ((finrank ℝ E : ℝ) ^ k * (‖f‖ * ((2 : ℝ) ^ ((α : ℝ) * j))⁻¹ * Mα))) := by
          gcongr
          exact hrev_j.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = K * ‖f‖ := by
          rw [hpow]
          have h2αj : (2 : ℝ) ^ ((α : ℝ) * j) ≠ 0 := by positivity
          simp only [K, pow_succ, div_pow, mul_pow]
          field_simp
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg f)

/-- **Every bounded `C^{k,α}` map lies in `𝒞^{k+α} = B^{k+α}_{∞,∞}`**, for every `k : ℕ` and
`α : ℝ≥0`. -/
theorem memBesov (f : CkHolderSpace k α E F) :
    (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)).MemBesov φ (k + α) ∞ ∞ := by
  obtain ⟨C, -, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (k := k) (α := α) φ
  choose g hg hgb using h f
  refine memBesov_iff.2 ⟨g, hg, memℓp_infty ⟨C * ‖f‖, ?_⟩⟩
  rintro _ ⟨j, rfl⟩
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  exact hgb j

/-- **The inclusion `C_b^{k,α} ⊆ 𝒞^{k+α}`** for every `k : ℕ` and `α : ℝ≥0`, as a continuous
linear map from the bounded `C^{k,α}` space to the Hölder–Zygmund space `B^{k+α}_{∞,∞}` built from
`φ`. -/
def toBesovSpace : CkHolderSpace k α E F →L[ℝ] BesovSpace F φ (k + α) ∞ ∞ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun f := (f.memBesov φ).toBesovSpace
      map_add' f g := BesovSpace.ext <| by
        simp [CkHolderSpace.toBoundedContinuousFunction_add, map_add, Lp.toTemperedDistribution_add]
      map_smul' c f := BesovSpace.ext <| by
        simp only [RingHom.id_apply, MemBesov.toDistr_toBesovSpace,
          CkHolderSpace.toBoundedContinuousFunction_smul]
        rw [← Complex.coe_smul c f.toBoundedContinuousFunction, map_smul,
          Lp.toTemperedDistribution_smul, ← Complex.coe_smul c ((f.memBesov φ).toBesovSpace),
          BesovSpace.toDistr_smul, MemBesov.toDistr_toBesovSpace] } <| by
    obtain ⟨C, -, hC⟩ := exists_rpow_mul_norm_littlewoodPaleyBlock_le (F := F) (k := k) (α := α) φ
    refine ⟨C, fun f ↦ ?_⟩
    set v := (f.memBesov φ).toBesovSpace
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [BesovSpace.norm_eq_ciSup]
    refine ciSup_le fun j ↦ ?_
    obtain ⟨g, hg, hgf⟩ := hC f j
    have hvg : v.block j = g := Lp.toTemperedDistribution_injective <| by
      simp only [BesovSpace.coe_block, ← hg, v, MemBesov.toDistr_toBesovSpace]
    rw [hvg]
    exact hgf

/-- The inclusion `CkHolderSpace.toBesovSpace` keeps the underlying tempered distribution. -/
@[simp]
theorem toDistr_toBesovSpace (f : CkHolderSpace k α E F) :
    (toBesovSpace φ f).toDistr =
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) := by
  simp [toBesovSpace]

end CkHolderSpace

namespace BesovSpace

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- `CkHolderSpace.toBesovSpace` is left inverse to `BesovSpace.toCkHolderSpace`. -/
@[simp]
theorem toBesovSpace_toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    CkHolderSpace.toBesovSpace φ (toCkHolderSpace F φ k hα0 hα1 u) = u :=
  ext <| by simp

/-- `BesovSpace.toCkHolderSpace` is left inverse to `CkHolderSpace.toBesovSpace`. -/
@[simp]
theorem toCkHolderSpace_toBesovSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    toCkHolderSpace F φ k hα0 hα1 (CkHolderSpace.toBesovSpace φ f) = f :=
  (toCkHolderSpace_eq_iff φ k hα0 hα1).2 (by simp)

variable (F) in
/-- **Identification `𝒞^{k+α} ≃L[ℝ] C_b^{k,α}`** for `k : ℕ` and `0 < α < 1`: the Hölder–Zygmund
space `B^{k+α}_{∞,∞}` is continuously linearly equivalent to the bounded `C^{k,α}` space. -/
def ckHolderSpaceEquiv (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) :
    BesovSpace F φ (k + α) ∞ ∞ ≃L[ℝ] CkHolderSpace k α E F :=
  ContinuousLinearEquiv.equivOfInverse
    (toCkHolderSpace F φ k hα0 hα1) (CkHolderSpace.toBesovSpace φ)
    (toBesovSpace_toCkHolderSpace φ k hα0 hα1) (toCkHolderSpace_toBesovSpace φ k hα0 hα1)

/-- Forward evaluation of `BesovSpace.ckHolderSpaceEquiv` is `BesovSpace.toCkHolderSpace`. -/
@[simp]
theorem ckHolderSpaceEquiv_apply (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (u : BesovSpace F φ (k + α) ∞ ∞) :
    ckHolderSpaceEquiv F φ k hα0 hα1 u = toCkHolderSpace F φ k hα0 hα1 u :=
  (rfl)

/-- Inverse evaluation of `BesovSpace.ckHolderSpaceEquiv` is `CkHolderSpace.toBesovSpace`. -/
@[simp]
theorem ckHolderSpaceEquiv_symm_apply (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (f : CkHolderSpace k α E F) :
    (ckHolderSpaceEquiv F φ k hα0 hα1).symm f = CkHolderSpace.toBesovSpace φ f :=
  (rfl)

end BesovSpace

end TauCeti

namespace TemperedDistribution

variable (φ : ContDiffBump (0 : E)) {α : ℝ≥0}

/-- **Unbundled identification `𝒞^{k+α} = C_b^{k,α}`** for `k : ℕ` and `0 < α < 1`: a tempered
distribution lies in `B^{k+α}_{∞,∞}` exactly when it is the tempered distribution of a bounded
`C^{k,α}` map. -/
theorem memBesov_iff_exists_ckHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) {u : 𝓢'(E, F)} :
    u.MemBesov φ (k + α) ∞ ∞ ↔
      ∃ f : TauCeti.CkHolderSpace k α E F,
        (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u :=
  ⟨fun hu ↦ ⟨TauCeti.BesovSpace.toCkHolderSpace F φ k hα0 hα1 hu.toBesovSpace, by simp⟩,
    fun ⟨f, hf⟩ ↦ hf ▸ f.memBesov φ⟩

end TemperedDistribution
