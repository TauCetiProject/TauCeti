/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LaplacianSymbol
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# The resolvent `(1 - Δ)⁻¹` on `L²`

On a finite-dimensional real inner product space `E`, the Laplacian on `L²(E, F)` is the Fourier
multiplier with the nonpositive symbol `Λ(ξ) = -4π² ‖ξ‖²` (`TauCeti.laplacianSymbol`). So the
resolvent `P = (1 - Δ)⁻¹` is the Fourier multiplier with the symbol
`(1 - Λ(ξ))⁻¹ = (1 + 4π² ‖ξ‖²)⁻¹` (`TauCeti.laplacianResolventSymbol`), and
`Q = Δ (1 - Δ)⁻¹` is the Fourier multiplier with the symbol `Λ(ξ) (1 - Λ(ξ))⁻¹`
(`TauCeti.laplacianMulResolventSymbol`). Both symbols are real and bounded by `1`, so `P` and
`Q` are bounded self-adjoint operators on `L²` (`MeasureTheory.Lp.laplacianResolventCLM`,
`MeasureTheory.Lp.laplacianMulResolventCLM`).

The resolvent maps `L²` into the domain of the Laplacian: the distributional Laplacian of `P χ`
is the `L²` function `Q χ` for every `χ ∈ L²`
(`MeasureTheory.Lp.laplacian_laplacianResolventCLM_apply`). Its symbol does not vanish, so `P` is
injective (`MeasureTheory.Lp.laplacianResolventCLM_injective`).

## Main declarations

* `MeasureTheory.Lp.laplacianResolventCLM`: the resolvent `(1 - Δ)⁻¹` on `L²`.
* `MeasureTheory.Lp.laplacianMulResolventCLM`: the bounded operator `Δ (1 - Δ)⁻¹` on `L²`.
* `MeasureTheory.Lp.laplacian_laplacianResolventCLM_apply`: `Δ ((1 - Δ)⁻¹ χ) = Δ (1 - Δ)⁻¹ χ`.
* `MeasureTheory.Lp.isSelfAdjoint_laplacianResolventCLM`,
  `MeasureTheory.Lp.isSelfAdjoint_laplacianMulResolventCLM`: both are self-adjoint.
* `MeasureTheory.Lp.laplacianResolventCLM_injective`: the resolvent is injective.
-/

public section

noncomputable section

open scoped FourierTransform ENNReal SchwartzMap Laplacian
open MeasureTheory Filter

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- The symbol `(1 + 4π² ‖ξ‖²)⁻¹ = (1 - Λ(ξ))⁻¹` of the resolvent `(1 - Δ)⁻¹`, where `Λ` is the
symbol `-4π² ‖ξ‖²` of `Δ`. -/
def laplacianResolventSymbol (ξ : E) : ℝ :=
  (1 - laplacianSymbol ξ)⁻¹

/-- The symbol `Λ(ξ) (1 - Λ(ξ))⁻¹` of `Δ (1 - Δ)⁻¹`, where `Λ` is the symbol `-4π² ‖ξ‖²` of
`Δ`. -/
def laplacianMulResolventSymbol (ξ : E) : ℝ :=
  laplacianSymbol ξ * laplacianResolventSymbol ξ

theorem laplacianResolventSymbol_pos (ξ : E) : 0 < laplacianResolventSymbol ξ :=
  inv_pos.2 (by linarith [laplacianSymbol_nonpos ξ])

theorem continuous_laplacianResolventSymbol : Continuous (laplacianResolventSymbol (E := E)) :=
  (continuous_const.sub laplacianSymbol.continuous).inv₀ fun ξ ↦
    (by linarith [laplacianSymbol_nonpos ξ] : (0 : ℝ) < 1 - laplacianSymbol ξ).ne'

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The symbol of `(1 - Δ)⁻¹` is bounded by `1`. -/
theorem memLp_laplacianResolventSymbol :
    MemLp (fun ξ : E ↦ (laplacianResolventSymbol ξ : ℂ)) ∞ volume := by
  refine memLp_top_of_bound (Complex.continuous_ofReal.comp
    continuous_laplacianResolventSymbol).aestronglyMeasurable 1 (Eventually.of_forall fun ξ ↦ ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg (laplacianResolventSymbol_pos ξ).le]
  exact inv_le_one_of_one_le₀ (by linarith [laplacianSymbol_nonpos ξ])

/-- The symbol of `Δ (1 - Δ)⁻¹` is bounded by `1`. -/
theorem memLp_laplacianMulResolventSymbol :
    MemLp (fun ξ : E ↦ (laplacianMulResolventSymbol ξ : ℂ)) ∞ volume := by
  refine memLp_top_of_bound (Complex.continuous_ofReal.comp
    (laplacianSymbol.continuous.mul continuous_laplacianResolventSymbol)).aestronglyMeasurable 1
    (Eventually.of_forall fun ξ ↦ ?_)
  have hl := laplacianSymbol_nonpos ξ
  rw [Complex.norm_real, Real.norm_eq_abs, laplacianMulResolventSymbol, laplacianResolventSymbol,
    ← div_eq_mul_inv, abs_div, abs_of_nonpos hl, abs_of_pos (by linarith),
    div_le_one (by linarith)]
  linarith

end TauCeti

namespace MeasureTheory.Lp

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The resolvent `(1 - Δ)⁻¹` on `L²(E, F)`, the Fourier multiplier with symbol
`TauCeti.laplacianResolventSymbol`. -/
def laplacianResolventCLM : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  fourierMultiplierCLM F (memLp_laplacianResolventSymbol.toLp _)

/-- The bounded operator `Δ (1 - Δ)⁻¹` on `L²(E, F)`, the Fourier multiplier with symbol
`TauCeti.laplacianMulResolventSymbol`. -/
def laplacianMulResolventCLM : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  fourierMultiplierCLM F (memLp_laplacianMulResolventSymbol.toLp _)

variable {F}

/-- **The resolvent maps `L²` into the domain of the Laplacian**: the distributional Laplacian of
`(1 - Δ)⁻¹ χ` is the `L²` function `Δ (1 - Δ)⁻¹ χ`. -/
theorem laplacian_laplacianResolventCLM_apply (χ : Lp F 2 (volume : Measure E)) :
    Δ ((laplacianResolventCLM F χ : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (laplacianMulResolventCLM F χ : 𝓢'(E, F)) := by
  refine (laplacian_toTemperedDistribution_eq_iff _ _).2 ?_
  filter_upwards [coeFn_fourier_fourierMultiplierCLM_toLp χ memLp_laplacianMulResolventSymbol,
    coeFn_fourier_fourierMultiplierCLM_toLp χ memLp_laplacianResolventSymbol] with ξ h₁ h₂
  rw [laplacianMulResolventCLM, laplacianResolventCLM, h₁, h₂, smul_smul,
    laplacianMulResolventSymbol, Complex.ofReal_mul]

/-- The resolvent `(1 - Δ)⁻¹` is self-adjoint, since its symbol is real. -/
theorem isSelfAdjoint_laplacianResolventCLM :
    IsSelfAdjoint (laplacianResolventCLM (E := E) F) :=
  isSelfAdjoint_fourierMultiplierCLM
    (star_eq_self_of_ae_eq_ofReal memLp_laplacianResolventSymbol.coeFn_toLp)

/-- The operator `Δ (1 - Δ)⁻¹` is self-adjoint, since its symbol is real. -/
theorem isSelfAdjoint_laplacianMulResolventCLM :
    IsSelfAdjoint (laplacianMulResolventCLM (E := E) F) :=
  isSelfAdjoint_fourierMultiplierCLM
    (star_eq_self_of_ae_eq_ofReal memLp_laplacianMulResolventSymbol.coeFn_toLp)

/-- The resolvent `(1 - Δ)⁻¹` is injective on `L²`, since its symbol does not vanish. -/
theorem laplacianResolventCLM_injective :
    Function.Injective (laplacianResolventCLM (E := E) F) := by
  refine (injective_iff_map_eq_zero (laplacianResolventCLM (E := E) F)).2 fun x hx ↦ ?_
  have h := coeFn_fourier_fourierMultiplierCLM_toLp x memLp_laplacianResolventSymbol
  rw [← laplacianResolventCLM, hx, FourierTransform.fourier_zero] at h
  have hx' : 𝓕 x = 0 := by
    refine eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [h, coeFn_zero F 2 (volume : Measure E)] with ξ h₁ h₂
    rw [h₂, Pi.zero_apply, eq_comm, smul_eq_zero] at h₁
    exact h₁.resolve_left (Complex.ofReal_ne_zero.2 (laplacianResolventSymbol_pos ξ).ne')
  simpa using congrArg 𝓕⁻ hx'

end MeasureTheory.Lp
