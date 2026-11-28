/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Homogeneous Sobolev seminorms of `L²` functions

For a function `f ∈ L²(E; F)` on a finite-dimensional real inner product space `E`, with values in
a complex Hilbert space `F`, and a real `s`, the homogeneous Sobolev seminorm is

`|f|_{\dot H^s} = ‖ ‖2πξ‖ˢ 𝓕 f ‖_{L²}`,

where `𝓕` is Mathlib's Fourier transform on `L²`, normalized by `𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`.
In this normalization the derivative `∂ₘ` has symbol `2πi⟪ξ, m⟫`, so the factor `2π` makes
`|f|_{\dot H^1}` the `L²` norm of the gradient of `f`. The seminorm is recorded as an extended
nonnegative real, `MeasureTheory.Lp.eHomogeneousSobolevNorm f s`, which is infinite exactly when
`‖2πξ‖ˢ 𝓕 f` is not square integrable; no homogeneous Sobolev space is formed. These seminorms
measure the size of initial data in scale-invariant form: under `f ↦ f(λ ·)` the seminorm
`|f|_{\dot H^s}` scales by `λ^{s - d/2}`, so for the Navier–Stokes equations in dimension three the
critical one is `|u₀|_{\dot H^{1/2}}`.

## Main declarations

* `MeasureTheory.Lp.eHomogeneousSobolevNorm f s`: the seminorm `|f|_{\dot H^s}`.
* `MeasureTheory.Lp.eHomogeneousSobolevNorm_sq`: for `s ≥ 0`,
  `|f|²_{\dot H^s} = ∫ (2π‖ξ‖)^{2s} ‖𝓕 f(ξ)‖² dξ`.
* `MeasureTheory.Lp.eHomogeneousSobolevNorm_zero`: Plancherel, `|f|_{\dot H^0} = ‖f‖_{L²}`.
* `MeasureTheory.Lp.eHomogeneousSobolevNorm_one_sq`: if the distributional derivatives
  `∂_{bᵢ} f` along an orthonormal basis `(bᵢ)` are the `L²` functions `dᵢ`, then
  `|f|²_{\dot H^1} = ∑ᵢ ‖dᵢ‖²_{L²}`, the squared `L²` norm of the gradient.
* `MeasureTheory.Lp.eHomogeneousSobolevNorm_le_rpow_mul_rpow`: the interpolation inequality
  `|f|_{\dot H^{(1-θ)s₀ + θs₁}} ≤ |f|_{\dot H^{s₀}}^{1-θ} |f|_{\dot H^{s₁}}^θ` for `s₀, s₁ ≥ 0`
  and `θ ∈ [0, 1]`.
* `MeasureTheory.Lp.eHomogeneousSobolevNorm_half_sq_le`: its case
  `|f|²_{\dot H^{1/2}} ≤ ‖f‖_{L²} |f|_{\dot H^1}`.

## References

* T. Tao, *254A: Incompressible fluid equations*, lecture notes, 2018, Notes 1: the homogeneous
  Sobolev norms of the critical Navier–Stokes theory.
* H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, §1.3.1: homogeneous Sobolev spaces and their interpolation
  inequality.
-/

public section

noncomputable section

namespace MeasureTheory.Lp

open Real TemperedDistribution
open scoped ENNReal FourierTransform LineDeriv RealInnerProductSpace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The **homogeneous Sobolev seminorm** `|f|_{\dot H^s} = ‖ ‖2πξ‖ˢ 𝓕 f ‖_{L²}` of `f ∈ L²(E; F)`,
as an extended nonnegative real. It is infinite when `‖2πξ‖ˢ 𝓕 f` is not square integrable. With the
factor `2π`, `|f|_{\dot H^1}` is the `L²` norm of the gradient of `f`
(`MeasureTheory.Lp.eHomogeneousSobolevNorm_one_sq`). -/
def eHomogeneousSobolevNorm (f : Lp F 2 (volume : Measure E)) (s : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun ξ ↦ (2 * π * ‖ξ‖) ^ s • (𝓕 f : Lp F 2 (volume : Measure E)) ξ) 2 volume

/-- The defining formula `|f|_{\dot H^s} = ‖ ‖2πξ‖ˢ 𝓕 f ‖_{L²}`. -/
theorem eHomogeneousSobolevNorm_def (f : Lp F 2 (volume : Measure E)) (s : ℝ) :
    eHomogeneousSobolevNorm f s =
      eLpNorm (fun ξ ↦ (2 * π * ‖ξ‖) ^ s • (𝓕 f : Lp F 2 (volume : Measure E)) ξ) 2 volume :=
  (rfl)

/-- **The Fourier integral of a homogeneous Sobolev seminorm.** For `s ≥ 0`,
`|f|²_{\dot H^s} = ∫ (2π‖ξ‖)^{2s} ‖𝓕 f(ξ)‖² dξ`. -/
theorem eHomogeneousSobolevNorm_sq {s : ℝ} (hs : 0 ≤ s) (f : Lp F 2 (volume : Measure E)) :
    eHomogeneousSobolevNorm f s ^ 2 = ∫⁻ ξ, ENNReal.ofReal (2 * π * ‖ξ‖) ^ (2 * s) *
      ‖(𝓕 f : Lp F 2 (volume : Measure E)) ξ‖ₑ ^ 2 := by
  have hmeas : AEStronglyMeasurable
      (fun ξ : E ↦ (2 * π * ‖ξ‖) ^ s • (𝓕 f : Lp F 2 (volume : Measure E)) ξ) volume :=
    (by fun_prop : Measurable fun ξ : E ↦ (2 * π * ‖ξ‖) ^ s).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hmeas
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [eHomogeneousSobolevNorm_def, h]
  refine lintegral_congr fun ξ ↦ ?_
  rw [eNorm_smul, Real.eNorm_of_nonneg (by positivity), mul_pow,
    ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hs, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul, Nat.cast_ofNat, mul_comm s]

/-- **Plancherel's identity** for the homogeneous seminorm of order zero:
`|f|_{\dot H^0} = ‖f‖_{L²}`. -/
@[simp]
theorem eHomogeneousSobolevNorm_zero (f : Lp F 2 (volume : Measure E)) :
    eHomogeneousSobolevNorm f 0 = ‖f‖ₑ := by
  simp only [eHomogeneousSobolevNorm_def, Real.rpow_zero, one_smul]
  rw [← Lp.eNorm_def, ← ofReal_norm, Lp.norm_fourier_eq, ofReal_norm]

/-- **The homogeneous seminorm of order one is the `L²` norm of the gradient.** If `(bᵢ)` is an
orthonormal basis of `E` and the distributional derivatives `∂_{bᵢ} f` of `f ∈ L²` are the `L²`
functions `dᵢ`, then `|f|²_{\dot H^1} = ∑ᵢ ‖dᵢ‖²_{L²}`. -/
theorem eHomogeneousSobolevNorm_one_sq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : Lp F 2 (volume : Measure E)) {d : ι → Lp F 2 (volume : Measure E)}
    (hd : ∀ i, ∂_{b i} (f : 𝓢'(E, F)) = d i) :
    eHomogeneousSobolevNorm f 1 ^ 2 = ∑ i, ‖d i‖ₑ ^ 2 := by
  -- On the Fourier side `‖𝓕 dᵢ(ξ)‖² = (2π)² ⟪ξ, bᵢ⟫² ‖𝓕 f(ξ)‖²`, and `∑ᵢ ⟪ξ, bᵢ⟫² = ‖ξ‖²`.
  have hfour (g : Lp F 2 (volume : Measure E)) :
      ‖g‖ₑ ^ 2 = ∫⁻ ξ, ‖(𝓕 g : Lp F 2 (volume : Measure E)) ξ‖ₑ ^ 2 := by
    simpa using eHomogeneousSobolevNorm_sq le_rfl g
  have hv := Lp.fourier_toTemperedDistribution_eq f
  have hpt (i : ι) : (fun ξ ↦ ‖(𝓕 (d i) : Lp F 2 (volume : Measure E)) ξ‖ₑ ^ 2) =ᵐ[volume]
      fun ξ ↦ ENNReal.ofReal ((2 * π) ^ 2 * ⟪ξ, b i⟫ ^ 2) *
        ‖(𝓕 f : Lp F 2 (volume : Measure E)) ξ‖ₑ ^ 2 := by
    filter_upwards [Lp.fourier_ae_eq_of_lineDerivOp_eq hv (hd i)] with ξ hξ
    rw [hξ, eNorm_smul, mul_pow, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 2
    simp [Complex.norm_real, mul_pow, abs_of_pos pi_pos]
  simp_rw [hfour, fun i ↦ lintegral_congr_ae (hpt i)]
  rw [← lintegral_finsetSum' _ fun i _ ↦ by fun_prop, eHomogeneousSobolevNorm_sq zero_le_one]
  refine lintegral_congr fun ξ ↦ ?_
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity, ← Finset.mul_sum,
    b.sum_sq_inner_left, mul_one, ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity), mul_pow]

/-- **Interpolation of homogeneous seminorms.** For `s₀, s₁ ≥ 0` and `θ ∈ [0, 1]`,
`|f|_{\dot H^{(1-θ)s₀ + θs₁}} ≤ |f|_{\dot H^{s₀}}^{1-θ} |f|_{\dot H^{s₁}}^θ`: the map
`s ↦ log |f|_{\dot H^s}` is convex on `[0, ∞)`. -/
theorem eHomogeneousSobolevNorm_le_rpow_mul_rpow {s₀ s₁ θ : ℝ} (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (f : Lp F 2 (volume : Measure E)) :
    eHomogeneousSobolevNorm f ((1 - θ) * s₀ + θ * s₁) ≤
      eHomogeneousSobolevNorm f s₀ ^ (1 - θ) * eHomogeneousSobolevNorm f s₁ ^ θ := by
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.2 hθ₁
  have hsq (x : ℝ≥0∞) (r : ℝ) : (x ^ r) ^ 2 = (x ^ 2) ^ r := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast x, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      mul_comm]
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, hsq, hsq,
    eHomogeneousSobolevNorm_sq (by positivity), eHomogeneousSobolevNorm_sq hs₀,
    eHomogeneousSobolevNorm_sq hs₁]
  -- Hölder's inequality with exponents `1/(1-θ)` and `1/θ` for the measure `‖𝓕 f‖² dξ`.
  refine le_of_eq_of_le (lintegral_congr fun ξ ↦ ?_)
    (ENNReal.lintegral_mul_norm_pow_le (by fun_prop) (by fun_prop) hθ' hθ₀ (sub_add_cancel 1 θ))
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ', ENNReal.mul_rpow_of_nonneg _ _ hθ₀, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, mul_mul_mul_comm, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity)
    (by positivity), ← ENNReal.rpow_add_of_nonneg _ _ hθ' hθ₀, sub_add_cancel, ENNReal.rpow_one]
  ring_nf

/-- **The interpolation inequality at order one half**:
`|f|²_{\dot H^{1/2}} ≤ ‖f‖_{L²} |f|_{\dot H^1}`.
Together with `MeasureTheory.Lp.eHomogeneousSobolevNorm_one_sq` this is
`|f|²_{\dot H^{1/2}} ≤ ‖f‖_{L²} ‖∇f‖_{L²}`. -/
theorem eHomogeneousSobolevNorm_half_sq_le (f : Lp F 2 (volume : Measure E)) :
    eHomogeneousSobolevNorm f (1 / 2) ^ 2 ≤ ‖f‖ₑ * eHomogeneousSobolevNorm f 1 := by
  have h := eHomogeneousSobolevNorm_le_rpow_mul_rpow le_rfl zero_le_one (θ := 1 / 2)
    (by norm_num) (by norm_num) f
  rw [show (1 - 1 / 2 : ℝ) * 0 + 1 / 2 * 1 = 1 / 2 by norm_num,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, eHomogeneousSobolevNorm_zero,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  calc _ ≤ ((‖f‖ₑ * eHomogeneousSobolevNorm f 1) ^ (1 / 2 : ℝ)) ^ 2 := ENNReal.pow_le_pow_left h
    _ = _ := by rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

end MeasureTheory.Lp
