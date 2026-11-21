/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Fourier.L2Multiplier
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# The Fourier symbols of the Laplacian and of its square root

In Mathlib's normalization of the Fourier transform, `𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, the
derivative `∂ᵥ` is the Fourier multiplier with symbol `2πi⟪ξ, v⟫`, so the Laplacian `Δ` is the
Fourier multiplier with the real symbol `-4π² ‖ξ‖²`, and its nonnegative square root
`D = √(-Δ)` is the Fourier multiplier with the real symbol `2π ‖ξ‖`. These are the phases of the
free Schrödinger propagator `exp(itΔ)` and of the half-wave propagators `exp(±itD)`.

The symbols are bundled as continuous maps, the form in which `TauCeti.phasePropagator` takes
its phase. On Schwartz functions the Laplacian is the multiplier with symbol
`TauCeti.laplacianSymbol` (`SchwartzMap.laplacian_eq_fourierMultiplierCLM_laplacianSymbol`, from
Mathlib's `SchwartzMap.laplacian_eq_fourierMultiplierCLM`). The symbol of `D` is not smooth at the
origin, so `D` is not a multiplier on Schwartz functions; its relation to the Laplacian is the
symbol identity `(2π ‖ξ‖)² = -(-4π² ‖ξ‖²)` (`TauCeti.sq_sqrtNegLaplacianSymbol`).

## Main declarations

* `TauCeti.laplacianSymbol`: the symbol `-4π² ‖ξ‖²` of the Laplacian.
* `SchwartzMap.laplacian_eq_fourierMultiplierCLM_laplacianSymbol`: on Schwartz functions, `Δ` is the
  Fourier multiplier with symbol `TauCeti.laplacianSymbol`.
* `SchwartzMap.fourier_laplacian_apply_eq_laplacianSymbol_smul`: pointwise on the Fourier side,
  `𝓕 (Δ u) ξ = -4π² ‖ξ‖² 𝓕 u ξ` for Schwartz functions `u`.
* `TauCeti.hasTemperateGrowth_laplacianSymbol`: it has temperate growth.
* `TauCeti.sqrtNegLaplacianSymbol`: the symbol `2π ‖ξ‖` of `√(-Δ)`.
* `TauCeti.sq_sqrtNegLaplacianSymbol`: its square is the symbol of `-Δ`.
* `TauCeti.laplacian_fourier` and `TauCeti.laplacian_fourierInv`: the Laplacian of the Fourier
  integral `𝓕 h`, or `𝓕⁻ h`, of a function `h` with integrable moments of order at most two is the
  Fourier integral of `-4π² ‖ξ‖² h`. No smoothness of `h` is needed.
* `MeasureTheory.Lp.laplacian_toTemperedDistribution_eq_iff`: for `f, h ∈ L²`, the distributional
  Laplacian of `f` is `h` exactly when `𝓕 h = -4π² ‖ξ‖² • 𝓕 f` almost everywhere, for the
  Fourier transform on `L²`.
* `MeasureTheory.Lp.laplacian_fourierMultiplierCLM_apply`: every `L²` Fourier multiplier commutes
  with `Δ`: if `Δ f = h ∈ L²`, then `Δ (T_m f) = T_m h`.
* `MeasureTheory.Lp.re_inner_nonpos_of_laplacian_toTemperedDistribution_eq`: `-Δ` is nonnegative,
  `re ⟪f, Δ f⟫ ≤ 0` whenever `Δ f ∈ L²`.
-/

public section

noncomputable section

open scoped Laplacian SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal
open Real MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The symbol `ξ ↦ -4π² ‖ξ‖²` of the Laplacian, in Mathlib's normalization of the Fourier
transform. -/
def laplacianSymbol : C(E, ℝ) :=
  ⟨fun ξ ↦ -(4 * π ^ 2 * ‖ξ‖ ^ 2), by fun_prop⟩

@[simp]
theorem laplacianSymbol_apply (ξ : E) : laplacianSymbol ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2) :=
  (rfl)

/-- The symbol `ξ ↦ 2π ‖ξ‖` of `D = √(-Δ)`, in Mathlib's normalization of the Fourier
transform. -/
def sqrtNegLaplacianSymbol : C(E, ℝ) :=
  ⟨fun ξ ↦ 2 * π * ‖ξ‖, by fun_prop⟩

@[simp]
theorem sqrtNegLaplacianSymbol_apply (ξ : E) : sqrtNegLaplacianSymbol ξ = 2 * π * ‖ξ‖ :=
  (rfl)

theorem sqrtNegLaplacianSymbol_nonneg (ξ : E) : 0 ≤ sqrtNegLaplacianSymbol ξ := by
  rw [sqrtNegLaplacianSymbol_apply]
  positivity

/-- `D² = -Δ` on the level of symbols. -/
theorem sq_sqrtNegLaplacianSymbol (ξ : E) :
    sqrtNegLaplacianSymbol ξ ^ 2 = -laplacianSymbol ξ := by
  rw [sqrtNegLaplacianSymbol_apply, laplacianSymbol_apply]
  ring

section Homogeneity

variable [NormedSpace ℝ E]

/-- The symbol of the Laplacian is homogeneous of degree `2`. -/
theorem laplacianSymbol_smul (c : ℝ) (ξ : E) :
    laplacianSymbol (c • ξ) = c ^ 2 * laplacianSymbol ξ := by
  rw [laplacianSymbol_apply, laplacianSymbol_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The symbol of `√(-Δ)` is positively homogeneous of degree `1`. -/
theorem sqrtNegLaplacianSymbol_smul (c : ℝ) (ξ : E) :
    sqrtNegLaplacianSymbol (c • ξ) = |c| * sqrtNegLaplacianSymbol ξ := by
  rw [sqrtNegLaplacianSymbol_apply, sqrtNegLaplacianSymbol_apply, norm_smul, Real.norm_eq_abs]
  ring

end Homogeneity

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The symbol of the Laplacian has temperate growth, so it is a Fourier multiplier on Schwartz
functions. -/
@[fun_prop]
theorem hasTemperateGrowth_laplacianSymbol : (laplacianSymbol : E → ℝ).HasTemperateGrowth := by
  have h : (laplacianSymbol : E → ℝ) = fun ξ ↦ -(4 * π ^ 2) * ‖ξ‖ ^ 2 := by
    ext ξ
    rw [laplacianSymbol_apply, neg_mul]
  rw [h]
  fun_prop

/-- On Schwartz functions, the Laplacian is the Fourier multiplier with symbol
`TauCeti.laplacianSymbol`. -/
theorem _root_.SchwartzMap.laplacian_eq_fourierMultiplierCLM_laplacianSymbol (f : 𝓢(E, F)) :
    Δ f = SchwartzMap.fourierMultiplierCLM F (laplacianSymbol : E → ℝ) f := by
  have h : (laplacianSymbol : E → ℝ) = (-(2 * π) ^ 2 : ℝ) • fun ξ : E ↦ ‖ξ‖ ^ 2 := by
    ext ξ
    simp only [laplacianSymbol_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM, h,
    SchwartzMap.fourierMultiplierCLM_smul (Function.hasTemperateGrowth_norm_sq E),
    _root_.smul_apply]

omit [CompleteSpace F] in
/-- `𝓕 (Δ u) ξ = -4π² ‖ξ‖² 𝓕 u ξ` for Schwartz functions, with the symbol of the Laplacian. -/
theorem _root_.SchwartzMap.fourier_laplacian_apply_eq_laplacianSymbol_smul (u : 𝓢(E, F))
    (ξ : E) : 𝓕 (Δ u) ξ = (laplacianSymbol ξ : ℂ) • 𝓕 u ξ := by
  rw [SchwartzMap.fourier_laplacian_apply, ← Complex.coe_smul]
  congr 1
  push_cast [laplacianSymbol_apply]
  ring

omit [CompleteSpace F] in
/-- **The Laplacian of a Fourier integral.** If `h` has integrable moments `‖ξ‖ⁿ ‖h ξ‖` of order
`n ≤ 2`, then the Laplacian of `𝓕 h` is the Fourier integral of `-4π² ‖ξ‖² h`. -/
theorem laplacian_fourier {h : E → F} (hh : ∀ n ≤ 2, Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖h ξ‖))
    (hm : AEStronglyMeasurable h) :
    Δ (𝓕 h) = 𝓕 (fun ξ ↦ (laplacianSymbol ξ : ℂ) • h ξ) := by
  ext x
  have hint : Integrable fun v ↦ 𝐞 (-inner ℝ v x) •
      VectorFourier.fourierPowSMulRight (innerSL ℝ) h v 2 :=
    (Real.fourierIntegral_convergent_iff x).2
      (VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hh 2 le_rfl) hm)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    Real.iteratedFDeriv_fourier (fun n hn ↦ hh n (by exact_mod_cast hn)) hm le_rfl]
  simp only [Real.fourier_eq, ContinuousMultilinearMap.integral_apply hint]
  rw [← integral_finsetSum _ fun i _ ↦ ?_]; swap
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) F _).integrable_comp hint
  congr 1 with v
  -- The second derivative of `𝐞 (-⟪v, x⟫)` along `bᵢ` is `(-2πi ⟪v, bᵢ⟫)²` times it, and the
  -- squares `⟪v, bᵢ⟫²` sum to `‖v‖²` over an orthonormal basis.
  have hsum : ∑ i, innerSL ℝ v ((stdOrthonormalBasis ℝ E) i) *
      innerSL ℝ v ((stdOrthonormalBasis ℝ E) i) = ‖v‖ ^ 2 := by
    simp only [innerSL_apply_apply, ← sq, (stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  simp only [Circle.smul_def, smul_apply, VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← Finset.sum_smul, hsum]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  -- The scalar identity `(-2πi)² ‖v‖² = -4π² ‖v‖²`.
  push_cast [laplacianSymbol_apply]
  linear_combination (4 * π ^ 2 * ‖v‖ ^ 2 : ℂ) * Complex.I_sq

omit [CompleteSpace F] in
/-- **The Laplacian of an inverse Fourier integral.** If `h` has integrable moments
`‖ξ‖ⁿ ‖h ξ‖` of order `n ≤ 2`, then the Laplacian of `𝓕⁻ h` is the inverse Fourier integral of
`-4π² ‖ξ‖² h`. -/
theorem laplacian_fourierInv {h : E → F} (hh : ∀ n ≤ 2, Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖h ξ‖))
    (hm : AEStronglyMeasurable h) :
    Δ (𝓕⁻ h) = 𝓕⁻ (fun ξ ↦ (laplacianSymbol ξ : ℂ) • h ξ) := by
  have hh' : ∀ n ≤ 2, Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖h (-ξ)‖) := fun n hn ↦ by
    simpa using (hh n hn).comp_neg
  rw [Real.fourierInv_eq_fourier_comp_neg,
    laplacian_fourier hh' (hm.comp_measurePreserving (Measure.measurePreserving_neg volume)),
    Real.fourierInv_eq_fourier_comp_neg]
  simp [laplacianSymbol_apply]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The Laplacian of an `L²` function on the Fourier side.** For `f, h ∈ L²`, the distributional
Laplacian of `f` is `h` exactly when the Fourier transform of `h` is `-4π² ‖ξ‖²` times that of `f`
almost everywhere. -/
theorem _root_.MeasureTheory.Lp.laplacian_toTemperedDistribution_eq_iff
    (f h : Lp F 2 (volume : Measure E)) :
    Δ (f : 𝓢'(E, F)) = (h : 𝓢'(E, F)) ↔
      (𝓕 h : Lp F 2 (volume : Measure E)) =ᵐ[volume]
        fun ξ ↦ (laplacianSymbol ξ : ℂ) • (𝓕 f : Lp F 2 (volume : Measure E)) ξ := by
  have hg : (fun ξ : E ↦ ((laplacianSymbol ξ : ℝ) : ℂ)).HasTemperateGrowth := by
    simp only [laplacianSymbol_apply]
    fun_prop
  -- On the Fourier side, `Δ` is multiplication by its symbol.
  have hF : 𝓕 (Δ (f : 𝓢'(E, F))) = TemperedDistribution.smulLeftCLM F
      (fun ξ : E ↦ ((laplacianSymbol ξ : ℝ) : ℂ))
        ((𝓕 f : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    have hsym : (fun ξ : E ↦ ((laplacianSymbol ξ : ℝ) : ℂ)) =
        ((-(2 * π) ^ 2 : ℝ) : ℂ) • fun ξ : E ↦ ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
      ext ξ
      simp only [laplacianSymbol_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    -- Move the scalar `-(2π)²` into the symbol of the multiplier, then cancel `𝓕 ∘ 𝓕⁻`.
    rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM,
      TemperedDistribution.fourierMultiplierCLM_apply, hsym,
      TemperedDistribution.smulLeftCLM_smul (by fun_prop)]
    simp [← Complex.coe_smul, Lp.fourier_toTemperedDistribution_eq]
  have hpair : ∀ φ : 𝓢(E, ℂ), 𝓕 (Δ (f : 𝓢'(E, F))) φ =
      ∫ ξ, φ ξ • (laplacianSymbol ξ : ℂ) • (𝓕 f : Lp F 2 (volume : Measure E)) ξ := fun φ ↦ by
    rw [hF, Lp.smulLeftCLM_toTemperedDistribution_apply hg]
  have hloc : LocallyIntegrable (fun ξ ↦ (laplacianSymbol ξ : ℂ) •
      (𝓕 f : Lp F 2 (volume : Measure E)) ξ) volume :=
    ((Lp.memLp _).locallyIntegrable (by norm_num)).continuous_smul (by fun_prop)
  rw [← (FourierTransform.fourierEquiv ℂ 𝓢'(E, F)).injective.eq_iff]
  simp only [FourierTransform.fourierEquiv_apply, Lp.fourier_toTemperedDistribution_eq]
  constructor
  · intro heq
    exact Lp.ae_eq_of_toTemperedDistribution_apply_eq _ hloc fun φ ↦ heq ▸ hpair φ
  · intro hae
    ext φ
    rw [hpair, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ]

/-- **`L²` Fourier multipliers commute with `Δ`.** If the distributional Laplacian of `f ∈ L²` is
the `L²` function `h`, then the Laplacian of `T_m f` is `T_m h`, for every symbol `m ∈ L^∞`. -/
theorem _root_.MeasureTheory.Lp.laplacian_fourierMultiplierCLM_apply
    (m : Lp ℂ ∞ (volume : Measure E)) {f h : Lp F 2 (volume : Measure E)}
    (hfh : Δ (f : 𝓢'(E, F)) = (h : 𝓢'(E, F))) :
    Δ ((Lp.fourierMultiplierCLM F m f : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (Lp.fourierMultiplierCLM F m h : 𝓢'(E, F)) := by
  rw [Lp.laplacian_toTemperedDistribution_eq_iff] at hfh ⊢
  rw [Lp.fourier_fourierMultiplierCLM, Lp.fourier_fourierMultiplierCLM]
  filter_upwards [hfh, Lp.coeFn_lpSMul (r := 2) m (𝓕 f), Lp.coeFn_lpSMul (r := 2) m (𝓕 h)]
    with ξ h₁ h₂ h₃
  rw [h₂, h₃, Pi.smul_apply', Pi.smul_apply', h₁, smul_comm]

/-- **`-Δ` is nonnegative on `L²`.** If the distributional Laplacian of `f ∈ L²` is the `L²`
function `h`, then `re ⟪f, h⟫ ≤ 0`; indeed `-re ⟪f, Δ f⟫ = ∫ 4π² ‖ξ‖² ‖𝓕 f ξ‖² dξ`. -/
theorem _root_.MeasureTheory.Lp.re_inner_nonpos_of_laplacian_toTemperedDistribution_eq
    {f h : Lp F 2 (volume : Measure E)} (hfh : Δ (f : 𝓢'(E, F)) = (h : 𝓢'(E, F))) :
    (⟪f, h⟫).re ≤ 0 := by
  rw [← Lp.inner_fourier_eq, L2.inner_def, ← RCLike.re_to_complex,
    ← integral_re (L2.integrable_inner _ _)]
  refine integral_nonpos_of_ae ?_
  filter_upwards [(Lp.laplacian_toTemperedDistribution_eq_iff f h).1 hfh] with ξ hξ
  have hΔ : laplacianSymbol ξ ≤ 0 := by
    rw [laplacianSymbol_apply, neg_nonpos]
    positivity
  rw [Pi.zero_apply, hξ, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simpa [← Complex.ofReal_pow] using
    mul_nonpos_of_nonpos_of_nonneg hΔ (sq_nonneg ‖(𝓕 f : Lp F 2 (volume : Measure E)) ξ‖)

end TauCeti
