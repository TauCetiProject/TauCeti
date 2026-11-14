/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace

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
* `TauCeti.sqrtNegLaplacianSymbol`: the symbol `2π ‖ξ‖` of `√(-Δ)`.
* `TauCeti.sq_sqrtNegLaplacianSymbol`: its square is the symbol of `-Δ`.
* `SchwartzMap.coeFn_fourier_toLp_laplacian`: in `L²`, `𝓕 (Δφ) = -4π² ‖ξ‖² 𝓕 φ` for Schwartz
  `φ`.
-/

public section

noncomputable section

open scoped Laplacian SchwartzMap
open Real

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
/-- The symbol of the Laplacian has temperate growth. -/
theorem hasTemperateGrowth_laplacianSymbol : (laplacianSymbol : E → ℝ).HasTemperateGrowth := by
  convert (Function.HasTemperateGrowth.const (-(4 * π ^ 2))).mul
    (Function.hasTemperateGrowth_norm_sq E) using 1
  ext ξ
  simp [laplacianSymbol_apply]

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

section L2

open MeasureTheory
open scoped FourierTransform

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- In `L²`, the Fourier transform of the Laplacian of a Schwartz function `φ` is
`𝓕 (Δφ) = -4π² ‖ξ‖² 𝓕 φ`, almost everywhere. -/
theorem _root_.SchwartzMap.coeFn_fourier_toLp_laplacian (φ : 𝓢(E, G)) :
    ((𝓕 ((Δ φ).toLp 2) : Lp G 2 (volume : Measure E)) : E → G) =ᵐ[volume]
      fun ξ ↦ (laplacianSymbol ξ : ℂ) • (𝓕 (φ.toLp 2) : Lp G 2 (volume : Measure E)) ξ := by
  have hΔ : 𝓕 (Δ φ) = SchwartzMap.smulLeftCLM G (laplacianSymbol : E → ℝ) (𝓕 φ) := by
    rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM_laplacianSymbol,
      SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  filter_upwards [(𝓕 (Δ φ)).coeFn_toLp 2 volume, (𝓕 φ).coeFn_toLp 2 volume] with ξ h₁ h₂
  rw [h₁, h₂, hΔ, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_laplacianSymbol,
    Complex.coe_smul]

end L2

end TauCeti
