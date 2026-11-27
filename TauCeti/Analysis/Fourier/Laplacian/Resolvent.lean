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
# The resolvent `(c - Δ)⁻¹` on `L²`

On a finite-dimensional real inner product space `E`, the Laplacian on `L²(E, F)` is the Fourier
multiplier with the nonpositive symbol `Λ(ξ) = -4π² ‖ξ‖²` (`TauCeti.laplacianSymbol`). So for
`c > 0` the resolvent `P_c = (c - Δ)⁻¹` is the Fourier multiplier with the symbol
`(c - Λ(ξ))⁻¹ = (c + 4π² ‖ξ‖²)⁻¹` (`TauCeti.laplacianResolventSymbol`), and
`Q_c = Δ (c - Δ)⁻¹` is the Fourier multiplier with the symbol `Λ(ξ) (c - Λ(ξ))⁻¹`
(`TauCeti.laplacianMulResolventSymbol`). Both symbols are real and bounded (by `c⁻¹` and `1`), so
`P_c` and `Q_c` are bounded self-adjoint operators on `L²`
(`MeasureTheory.Lp.laplacianResolventCLM`, `MeasureTheory.Lp.laplacianMulResolventCLM`).
The symbols satisfy `c (c - Λ)⁻¹ - Λ (c - Λ)⁻¹ = 1`, so `c P_c - Q_c = 1`
(`MeasureTheory.Lp.smul_laplacianResolventCLM_sub_laplacianMulResolventCLM`).

The resolvent maps `L²` into the domain of the Laplacian: the distributional Laplacian of `P_c χ`
is the `L²` function `Q_c χ` for every `χ ∈ L²`
(`MeasureTheory.Lp.laplacian_laplacianResolventCLM_apply`). Its symbol does not vanish, so `P_c`
is injective (`MeasureTheory.Lp.laplacianResolventCLM_injective`). On `L²` it agrees with the
resolvent `TemperedDistribution.laplacianResolvent F c` on tempered distributions
(`MeasureTheory.Lp.laplacianResolvent_toTemperedDistribution_eq`).

## Main declarations

* `MeasureTheory.Lp.laplacianResolventCLM`: the resolvent `(c - Δ)⁻¹` on `L²`.
* `MeasureTheory.Lp.laplacianMulResolventCLM`: the bounded operator `Δ (c - Δ)⁻¹` on `L²`.
* `MeasureTheory.Lp.coeFn_fourier_laplacianResolventCLM`,
  `MeasureTheory.Lp.coeFn_fourier_laplacianMulResolventCLM`: on the Fourier side both act as
  multiplication by their symbols.
* `MeasureTheory.Lp.laplacian_laplacianResolventCLM_apply`: `Δ ((c - Δ)⁻¹ χ) = Δ (c - Δ)⁻¹ χ`.
* `MeasureTheory.Lp.smul_laplacianResolventCLM_sub_laplacianMulResolventCLM`: `c P_c - Q_c = 1`,
  so `(c - Δ) P_c χ = χ`.
* `MeasureTheory.Lp.laplacianResolvent_toTemperedDistribution_eq`: `P_c` is the restriction to
  `L²` of the resolvent `TemperedDistribution.laplacianResolvent F c`.
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

/-- The symbol `(c + 4π² ‖ξ‖²)⁻¹ = (c - Λ(ξ))⁻¹` of the resolvent `(c - Δ)⁻¹`, where `Λ` is the
symbol `-4π² ‖ξ‖²` of `Δ`. -/
def laplacianResolventSymbol (c : ℝ) (ξ : E) : ℝ :=
  (c - laplacianSymbol ξ)⁻¹

/-- The symbol `Λ(ξ) (c - Λ(ξ))⁻¹` of `Δ (c - Δ)⁻¹`, where `Λ` is the symbol `-4π² ‖ξ‖²` of
`Δ`. -/
def laplacianMulResolventSymbol (c : ℝ) (ξ : E) : ℝ :=
  laplacianSymbol ξ * laplacianResolventSymbol c ξ

@[simp]
theorem laplacianResolventSymbol_apply (c : ℝ) (ξ : E) :
    laplacianResolventSymbol c ξ = (c + 4 * π ^ 2 * ‖ξ‖ ^ 2)⁻¹ := by
  rw [laplacianResolventSymbol, laplacianSymbol_apply, sub_neg_eq_add]

@[simp]
theorem laplacianMulResolventSymbol_apply (c : ℝ) (ξ : E) :
    laplacianMulResolventSymbol c ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2) / (c + 4 * π ^ 2 * ‖ξ‖ ^ 2) := by
  rw [laplacianMulResolventSymbol, laplacianResolventSymbol_apply, laplacianSymbol_apply,
    div_eq_mul_inv]

/-- The symbol identity `c (c - Λ)⁻¹ - Λ (c - Λ)⁻¹ = 1` behind
`c (c - Δ)⁻¹ - Δ (c - Δ)⁻¹ = 1`, for `c > 0`. -/
theorem mul_laplacianResolventSymbol_sub_laplacianMulResolventSymbol {c : ℝ} (hc : 0 < c)
    (ξ : E) : c * laplacianResolventSymbol c ξ - laplacianMulResolventSymbol c ξ = 1 := by
  rw [laplacianMulResolventSymbol, ← sub_mul, laplacianResolventSymbol,
    mul_inv_cancel₀ (by linarith [laplacianSymbol_nonpos ξ])]

theorem laplacianResolventSymbol_pos {c : ℝ} (hc : 0 < c) (ξ : E) :
    0 < laplacianResolventSymbol c ξ :=
  inv_pos.2 (by linarith [laplacianSymbol_nonpos ξ])

theorem continuous_laplacianResolventSymbol {c : ℝ} (hc : 0 < c) :
    Continuous (laplacianResolventSymbol (E := E) c) :=
  (continuous_const.sub laplacianSymbol.continuous).inv₀ fun ξ ↦
    (by linarith [laplacianSymbol_nonpos ξ] : (0 : ℝ) < c - laplacianSymbol ξ).ne'

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The symbol of `(c - Δ)⁻¹` is bounded by `c⁻¹`, for `c > 0`. -/
theorem memLp_laplacianResolventSymbol {c : ℝ} (hc : 0 < c) :
    MemLp (fun ξ : E ↦ (laplacianResolventSymbol c ξ : ℂ)) ∞ volume := by
  refine memLp_top_of_bound (Complex.continuous_ofReal.comp
    (continuous_laplacianResolventSymbol hc)).aestronglyMeasurable c⁻¹
    (Eventually.of_forall fun ξ ↦ ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg (laplacianResolventSymbol_pos hc ξ).le]
  exact inv_anti₀ hc (by linarith [laplacianSymbol_nonpos ξ])

/-- The symbol of `Δ (c - Δ)⁻¹` is bounded by `1`, for `c > 0`. -/
theorem memLp_laplacianMulResolventSymbol {c : ℝ} (hc : 0 < c) :
    MemLp (fun ξ : E ↦ (laplacianMulResolventSymbol c ξ : ℂ)) ∞ volume := by
  refine memLp_top_of_bound (Complex.continuous_ofReal.comp
    (laplacianSymbol.continuous.mul (continuous_laplacianResolventSymbol hc))).aestronglyMeasurable
    1 (Eventually.of_forall fun ξ ↦ ?_)
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
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {c : ℝ}

/-- The resolvent `(c - Δ)⁻¹` on `L²(E, F)`, for `c > 0`: the Fourier multiplier with symbol
`TauCeti.laplacianResolventSymbol c`. -/
def laplacianResolventCLM (hc : 0 < c) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  fourierMultiplierCLM F ((memLp_laplacianResolventSymbol hc).toLp _)

/-- The bounded operator `Δ (c - Δ)⁻¹` on `L²(E, F)`, for `c > 0`: the Fourier multiplier with
symbol `TauCeti.laplacianMulResolventSymbol c`. -/
def laplacianMulResolventCLM (hc : 0 < c) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  fourierMultiplierCLM F ((memLp_laplacianMulResolventSymbol hc).toLp _)

variable {F}

/-- The resolvent `(c - Δ)⁻¹` is the Fourier multiplier with symbol
`TauCeti.laplacianResolventSymbol c`. -/
theorem laplacianResolventCLM_eq_fourierMultiplierCLM (hc : 0 < c) :
    laplacianResolventCLM (E := E) F hc =
      fourierMultiplierCLM F ((memLp_laplacianResolventSymbol hc).toLp _) :=
  (rfl)

/-- The operator `Δ (c - Δ)⁻¹` is the Fourier multiplier with symbol
`TauCeti.laplacianMulResolventSymbol c`. -/
theorem laplacianMulResolventCLM_eq_fourierMultiplierCLM (hc : 0 < c) :
    laplacianMulResolventCLM (E := E) F hc =
      fourierMultiplierCLM F ((memLp_laplacianMulResolventSymbol hc).toLp _) :=
  (rfl)

/-- On the Fourier side, the resolvent `(c - Δ)⁻¹` is multiplication by its symbol
`(c + 4π² ‖ξ‖²)⁻¹`. -/
theorem coeFn_fourier_laplacianResolventCLM (hc : 0 < c) (χ : Lp F 2 (volume : Measure E)) :
    𝓕 (laplacianResolventCLM F hc χ) =ᵐ[volume]
      fun ξ ↦ (laplacianResolventSymbol c ξ : ℂ) • 𝓕 χ ξ :=
  coeFn_fourier_fourierMultiplierCLM_toLp χ (memLp_laplacianResolventSymbol hc)

/-- On the Fourier side, `Δ (c - Δ)⁻¹` is multiplication by its symbol
`-4π² ‖ξ‖² (c + 4π² ‖ξ‖²)⁻¹`. -/
theorem coeFn_fourier_laplacianMulResolventCLM (hc : 0 < c) (χ : Lp F 2 (volume : Measure E)) :
    𝓕 (laplacianMulResolventCLM F hc χ) =ᵐ[volume]
      fun ξ ↦ (laplacianMulResolventSymbol c ξ : ℂ) • 𝓕 χ ξ :=
  coeFn_fourier_fourierMultiplierCLM_toLp χ (memLp_laplacianMulResolventSymbol hc)

/-- **The resolvent maps `L²` into the domain of the Laplacian**: the distributional Laplacian of
`(c - Δ)⁻¹ χ` is the `L²` function `Δ (c - Δ)⁻¹ χ`. -/
theorem laplacian_laplacianResolventCLM_apply (hc : 0 < c) (χ : Lp F 2 (volume : Measure E)) :
    Δ ((laplacianResolventCLM F hc χ : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (laplacianMulResolventCLM F hc χ : 𝓢'(E, F)) := by
  refine (laplacian_toTemperedDistribution_eq_iff _ _).2 ?_
  filter_upwards [coeFn_fourier_laplacianMulResolventCLM hc χ,
    coeFn_fourier_laplacianResolventCLM hc χ] with ξ h₁ h₂
  rw [h₁, h₂, smul_smul, laplacianMulResolventSymbol, Complex.ofReal_mul]

/-- `c (c - Δ)⁻¹ - Δ (c - Δ)⁻¹ = 1` on `L²`: together with
`laplacian_laplacianResolventCLM_apply`, this says that `(c - Δ) (c - Δ)⁻¹ χ = χ`. -/
theorem smul_laplacianResolventCLM_sub_laplacianMulResolventCLM (hc : 0 < c) :
    (c : ℂ) • laplacianResolventCLM (E := E) F hc - laplacianMulResolventCLM F hc = 1 := by
  rw [laplacianResolventCLM_eq_fourierMultiplierCLM,
    laplacianMulResolventCLM_eq_fourierMultiplierCLM, ← fourierMultiplierCLM_smul,
    ← fourierMultiplierCLM_sub, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub,
    fourierMultiplierCLM_of_ae_eq_const (c := 1), one_smul, ContinuousLinearMap.one_def]
  filter_upwards [(((memLp_laplacianResolventSymbol (E := E) hc).const_smul (c : ℂ)).sub
    (memLp_laplacianMulResolventSymbol hc)).coeFn_toLp] with ξ h
  rw [h, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    mul_laplacianResolventSymbol_sub_laplacianMulResolventSymbol hc, Complex.ofReal_one]

/-- Pointwise form of `smul_laplacianResolventCLM_sub_laplacianMulResolventCLM`:
`c (c - Δ)⁻¹ χ - Δ (c - Δ)⁻¹ χ = χ`. -/
theorem smul_laplacianResolventCLM_apply_sub_laplacianMulResolventCLM_apply (hc : 0 < c)
    (χ : Lp F 2 (volume : Measure E)) :
    (c : ℂ) • laplacianResolventCLM F hc χ - laplacianMulResolventCLM F hc χ = χ := by
  simpa using congr($(smul_laplacianResolventCLM_sub_laplacianMulResolventCLM (E := E) (F := F)
    hc) χ)

/-- The resolvent `(c - Δ)⁻¹` on `L²` is the restriction of the resolvent
`TemperedDistribution.laplacianResolvent F c` on tempered distributions. -/
theorem laplacianResolvent_toTemperedDistribution_eq (hc : 0 < c)
    (χ : Lp F 2 (volume : Measure E)) :
    TemperedDistribution.laplacianResolvent F c (χ : 𝓢'(E, F)) =
      (laplacianResolventCLM F hc χ : 𝓢'(E, F)) := by
  conv_lhs => rw [← smul_laplacianResolventCLM_apply_sub_laplacianMulResolventCLM_apply hc χ,
    toTemperedDistribution_sub, toTemperedDistribution_smul,
    ← laplacian_laplacianResolventCLM_apply hc, sub_eq_neg_add, Complex.coe_smul]
  exact TemperedDistribution.laplacianResolvent_neg_laplacian_add_smul hc _

/-- The resolvent `(c - Δ)⁻¹` is self-adjoint, since its symbol is real. -/
theorem isSelfAdjoint_laplacianResolventCLM (hc : 0 < c) :
    IsSelfAdjoint (laplacianResolventCLM (E := E) F hc) :=
  isSelfAdjoint_fourierMultiplierCLM
    (star_eq_self_of_ae_eq_ofReal (memLp_laplacianResolventSymbol hc).coeFn_toLp)

/-- The operator `Δ (c - Δ)⁻¹` is self-adjoint, since its symbol is real. -/
theorem isSelfAdjoint_laplacianMulResolventCLM (hc : 0 < c) :
    IsSelfAdjoint (laplacianMulResolventCLM (E := E) F hc) :=
  isSelfAdjoint_fourierMultiplierCLM
    (star_eq_self_of_ae_eq_ofReal (memLp_laplacianMulResolventSymbol hc).coeFn_toLp)

/-- The resolvent `(c - Δ)⁻¹` is injective on `L²`, since its symbol does not vanish. -/
theorem laplacianResolventCLM_injective (hc : 0 < c) :
    Function.Injective (laplacianResolventCLM (E := E) F hc) := by
  refine (injective_iff_map_eq_zero (laplacianResolventCLM (E := E) F hc)).2 fun x hx ↦ ?_
  have h := coeFn_fourier_laplacianResolventCLM hc x
  rw [hx, FourierTransform.fourier_zero] at h
  have hx' : 𝓕 x = 0 := by
    refine eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [h, coeFn_zero F 2 (volume : Measure E)] with ξ h₁ h₂
    rw [h₂, Pi.zero_apply, eq_comm, smul_eq_zero] at h₁
    exact h₁.resolve_left (Complex.ofReal_ne_zero.2 (laplacianResolventSymbol_pos hc ξ).ne')
  simpa using congrArg 𝓕⁻ hx'

end MeasureTheory.Lp
