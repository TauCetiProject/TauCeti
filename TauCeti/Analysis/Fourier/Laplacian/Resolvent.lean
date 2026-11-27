/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
public import TauCeti.Analysis.Fourier.Laplacian.Symbol
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
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
`MeasureTheory.Lp.laplacianMulResolventCLM`). The symbols satisfy
`(1 - Λ)⁻¹ - Λ (1 - Λ)⁻¹ = 1`, so `P - Q = 1`
(`MeasureTheory.Lp.laplacianResolventCLM_sub_laplacianMulResolventCLM`).

The resolvent maps `L²` into the domain of the Laplacian: the distributional Laplacian of `P χ`
is the `L²` function `Q χ` for every `χ ∈ L²`
(`MeasureTheory.Lp.laplacian_laplacianResolventCLM_apply`). Its symbol does not vanish, so `P` is
injective (`MeasureTheory.Lp.laplacianResolventCLM_injective`). On `L²` it agrees with the
resolvent `TemperedDistribution.laplacianResolvent F 1` on tempered distributions
(`MeasureTheory.Lp.laplacianResolventCLM_toTemperedDistribution_eq`).

## Main declarations

* `MeasureTheory.Lp.laplacianResolventCLM`: the resolvent `(1 - Δ)⁻¹` on `L²`.
* `MeasureTheory.Lp.laplacianMulResolventCLM`: the bounded operator `Δ (1 - Δ)⁻¹` on `L²`.
* `MeasureTheory.Lp.coeFn_fourier_laplacianResolventCLM`,
  `MeasureTheory.Lp.coeFn_fourier_laplacianMulResolventCLM`: on the Fourier side both act as
  multiplication by their symbols.
* `MeasureTheory.Lp.laplacian_laplacianResolventCLM_apply`: `Δ ((1 - Δ)⁻¹ χ) = Δ (1 - Δ)⁻¹ χ`.
* `MeasureTheory.Lp.laplacianResolventCLM_sub_laplacianMulResolventCLM`: `P - Q = 1`, so
  `(1 - Δ) P χ = χ`.
* `MeasureTheory.Lp.laplacianResolventCLM_toTemperedDistribution_eq`: `P` is the restriction to
  `L²` of the resolvent `TemperedDistribution.laplacianResolvent F 1`.
* `MeasureTheory.Lp.isSelfAdjoint_laplacianResolventCLM`,
  `MeasureTheory.Lp.isSelfAdjoint_laplacianMulResolventCLM`: both are self-adjoint.
* `MeasureTheory.Lp.laplacianResolventCLM_injective`: the resolvent is injective.
-/

public section

noncomputable section

open scoped FourierTransform ENNReal SchwartzMap Laplacian
open MeasureTheory Filter Real

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

@[simp]
theorem laplacianResolventSymbol_apply (ξ : E) :
    laplacianResolventSymbol ξ = (1 + 4 * π ^ 2 * ‖ξ‖ ^ 2)⁻¹ := by
  rw [laplacianResolventSymbol, laplacianSymbol_apply, sub_neg_eq_add]

@[simp]
theorem laplacianMulResolventSymbol_apply (ξ : E) :
    laplacianMulResolventSymbol ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2) / (1 + 4 * π ^ 2 * ‖ξ‖ ^ 2) := by
  rw [laplacianMulResolventSymbol, laplacianResolventSymbol_apply, laplacianSymbol_apply,
    div_eq_mul_inv]

/-- The symbol identity `(1 - Λ)⁻¹ - Λ (1 - Λ)⁻¹ = 1` behind `(1 - Δ)⁻¹ - Δ (1 - Δ)⁻¹ = 1`. -/
theorem laplacianResolventSymbol_sub_laplacianMulResolventSymbol (ξ : E) :
    laplacianResolventSymbol ξ - laplacianMulResolventSymbol ξ = 1 := by
  rw [laplacianMulResolventSymbol, ← one_sub_mul, laplacianResolventSymbol,
    mul_inv_cancel₀ (by linarith [laplacianSymbol_nonpos ξ])]

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

/-- The resolvent `(1 - Δ)⁻¹` is the Fourier multiplier with symbol
`TauCeti.laplacianResolventSymbol`. -/
theorem laplacianResolventCLM_eq_fourierMultiplierCLM :
    laplacianResolventCLM (E := E) F =
      fourierMultiplierCLM F (memLp_laplacianResolventSymbol.toLp _) :=
  (rfl)

/-- The operator `Δ (1 - Δ)⁻¹` is the Fourier multiplier with symbol
`TauCeti.laplacianMulResolventSymbol`. -/
theorem laplacianMulResolventCLM_eq_fourierMultiplierCLM :
    laplacianMulResolventCLM (E := E) F =
      fourierMultiplierCLM F (memLp_laplacianMulResolventSymbol.toLp _) :=
  (rfl)

/-- On the Fourier side, the resolvent `(1 - Δ)⁻¹` is multiplication by its symbol
`(1 + 4π² ‖ξ‖²)⁻¹`. -/
theorem coeFn_fourier_laplacianResolventCLM (χ : Lp F 2 (volume : Measure E)) :
    𝓕 (laplacianResolventCLM F χ) =ᵐ[volume] fun ξ ↦ (laplacianResolventSymbol ξ : ℂ) • 𝓕 χ ξ :=
  coeFn_fourier_fourierMultiplierCLM_toLp χ memLp_laplacianResolventSymbol

/-- On the Fourier side, `Δ (1 - Δ)⁻¹` is multiplication by its symbol
`-4π² ‖ξ‖² (1 + 4π² ‖ξ‖²)⁻¹`. -/
theorem coeFn_fourier_laplacianMulResolventCLM (χ : Lp F 2 (volume : Measure E)) :
    𝓕 (laplacianMulResolventCLM F χ) =ᵐ[volume]
      fun ξ ↦ (laplacianMulResolventSymbol ξ : ℂ) • 𝓕 χ ξ :=
  coeFn_fourier_fourierMultiplierCLM_toLp χ memLp_laplacianMulResolventSymbol

/-- **The resolvent maps `L²` into the domain of the Laplacian**: the distributional Laplacian of
`(1 - Δ)⁻¹ χ` is the `L²` function `Δ (1 - Δ)⁻¹ χ`. -/
theorem laplacian_laplacianResolventCLM_apply (χ : Lp F 2 (volume : Measure E)) :
    Δ ((laplacianResolventCLM F χ : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (laplacianMulResolventCLM F χ : 𝓢'(E, F)) := by
  refine (laplacian_toTemperedDistribution_eq_iff _ _).2 ?_
  filter_upwards [coeFn_fourier_laplacianMulResolventCLM χ,
    coeFn_fourier_laplacianResolventCLM χ] with ξ h₁ h₂
  rw [h₁, h₂, smul_smul, laplacianMulResolventSymbol, Complex.ofReal_mul]

/-- `(1 - Δ)⁻¹ - Δ (1 - Δ)⁻¹ = 1` on `L²`: together with
`laplacian_laplacianResolventCLM_apply`, this says that `(1 - Δ) (1 - Δ)⁻¹ χ = χ`. -/
theorem laplacianResolventCLM_sub_laplacianMulResolventCLM :
    laplacianResolventCLM (E := E) F - laplacianMulResolventCLM F = 1 := by
  rw [laplacianResolventCLM_eq_fourierMultiplierCLM,
    laplacianMulResolventCLM_eq_fourierMultiplierCLM, ← fourierMultiplierCLM_sub,
    ← MemLp.toLp_sub, fourierMultiplierCLM_of_ae_eq_const (c := 1), one_smul,
    ContinuousLinearMap.one_def]
  filter_upwards [((memLp_laplacianResolventSymbol (E := E)).sub
    memLp_laplacianMulResolventSymbol).coeFn_toLp] with ξ h
  rw [h, Pi.sub_apply, ← Complex.ofReal_sub,
    laplacianResolventSymbol_sub_laplacianMulResolventSymbol, Complex.ofReal_one]

/-- Pointwise form of `laplacianResolventCLM_sub_laplacianMulResolventCLM`:
`(1 - Δ)⁻¹ χ - Δ (1 - Δ)⁻¹ χ = χ`. -/
theorem laplacianResolventCLM_apply_sub_laplacianMulResolventCLM_apply
    (χ : Lp F 2 (volume : Measure E)) :
    laplacianResolventCLM F χ - laplacianMulResolventCLM F χ = χ := by
  simpa using congr($(laplacianResolventCLM_sub_laplacianMulResolventCLM (E := E) (F := F)) χ)

/-- The resolvent `(1 - Δ)⁻¹` on `L²` is the restriction of the resolvent
`TemperedDistribution.laplacianResolvent F 1` on tempered distributions. -/
theorem laplacianResolventCLM_toTemperedDistribution_eq (χ : Lp F 2 (volume : Measure E)) :
    TemperedDistribution.laplacianResolvent F 1 (χ : 𝓢'(E, F)) =
      (laplacianResolventCLM F χ : 𝓢'(E, F)) := by
  conv_lhs => rw [← laplacianResolventCLM_apply_sub_laplacianMulResolventCLM_apply χ,
    toTemperedDistribution_sub, ← laplacian_laplacianResolventCLM_apply]
  exact TemperedDistribution.laplacianResolvent_one_sub_laplacian _

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
  have h := coeFn_fourier_laplacianResolventCLM x
  rw [hx, FourierTransform.fourier_zero] at h
  have hx' : 𝓕 x = 0 := by
    refine eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [h, coeFn_zero F 2 (volume : Measure E)] with ξ h₁ h₂
    rw [h₂, Pi.zero_apply, eq_comm, smul_eq_zero] at h₁
    exact h₁.resolve_left (Complex.ofReal_ne_zero.2 (laplacianResolventSymbol_pos ξ).ne')
  simpa using congrArg 𝓕⁻ hx'

end MeasureTheory.Lp
