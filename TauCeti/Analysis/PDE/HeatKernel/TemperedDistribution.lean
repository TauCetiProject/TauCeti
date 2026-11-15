/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution

/-!
# The heat semigroup on tempered distributions

On a finite-dimensional real inner product space `E`, the heat semigroup `e^{tΔ}`, `t ≥ 0`, is the
Fourier multiplier with symbol `exp(-4π² t ‖ξ‖²)`, in Mathlib's normalization
`𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx` of the Fourier transform. This symbol has temperate growth, so
`e^{tΔ}` is a continuous linear operator on all tempered distributions
(`TemperedDistribution.heatSemigroup`), and the semigroup law `e^{sΔ} e^{tΔ} = e^{(s+t)Δ}` is the
identity `exp(-4π² s ‖ξ‖²) exp(-4π² t ‖ξ‖²) = exp(-4π² (s + t) ‖ξ‖²)` of symbols.

For `t > 0` the symbol is a Schwartz function whose inverse Fourier transform is the heat kernel
`K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` (`TauCeti.fourierInv_exp_neg_mul_norm_sq`), so on the
tempered distribution of an `Lᵖ` function `f`, `1 ≤ p ≤ ∞`, the operator is convolution with
`K_t` (`TemperedDistribution.exists_heatSemigroup_eq_and_ae_eq_convolution`). Two consequences
are recorded:

* for `1 ≤ p < ∞` this operator extends the heat semigroup `TauCeti.heatSemigroup` on `Lᵖ`
  (`TemperedDistribution.heatSemigroup_toTemperedDistribution`);
* for every `1 ≤ p ≤ ∞`, including `p = ∞`, where there is no strongly continuous semigroup on
  `Lᵖ`, `e^{tΔ} f` is again an `Lᵖ` function with `‖e^{tΔ} f‖_p ≤ ‖f‖_p`
  (`TemperedDistribution.exists_heatSemigroup_eq_and_norm_le`), because `K_t ≥ 0` has mass one.

Working on `𝓢'` lets the heat semigroup act on spaces of distributions, such as the Besov spaces
`B^s_{p,q}` with `p = ∞`, whose elements need not be functions.

## Main declarations

* `TemperedDistribution.heatSemigroup`: the heat semigroup `e^{tΔ}` on `𝓢'(E, F)`.
* `TemperedDistribution.heatSemigroup_zero`,
  `TemperedDistribution.heatSemigroup_heatSemigroup_apply`:
  `e^{0Δ} = 1` and `e^{tΔ} e^{sΔ} = e^{(s+t)Δ}`.
* `TemperedDistribution.exists_heatSemigroup_eq_and_ae_eq_convolution`: for `t > 0`, `e^{tΔ}` is
  convolution with the heat kernel on every `Lᵖ`, `1 ≤ p ≤ ∞`.
* `TemperedDistribution.heatSemigroup_toTemperedDistribution`: agreement with the heat semigroup on
  `Lᵖ`, `p < ∞`.
* `TemperedDistribution.exists_heatSemigroup_eq_and_norm_le`: `e^{tΔ}` is a contraction on every
  `Lᵖ`, `1 ≤ p ≤ ∞`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Chapter 2 (the Fourier transform of the
  Gaussian, tempered distributions and Fourier multipliers).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.1.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped Convolution ENNReal NNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TemperedDistribution

open TauCeti

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (E F) in
/-- **The heat semigroup** `e^{tΔ}` on tempered distributions: the Fourier multiplier with symbol
`exp(-4π² t ‖ξ‖²)`, `t ≥ 0`. For `t > 0`, on the tempered distribution of an `Lᵖ` function,
`1 ≤ p ≤ ∞`, it is convolution with the heat kernel `heatKernel t`
(`TemperedDistribution.exists_heatSemigroup_eq_and_ae_eq_convolution`); for `1 ≤ p < ∞` it
extends `TauCeti.heatSemigroup` (`TemperedDistribution.heatSemigroup_toTemperedDistribution`). -/
def heatSemigroup (t : ℝ≥0) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F fun ξ ↦ ((rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ)

/-- Unfolding `TemperedDistribution.heatSemigroup`. -/
theorem heatSemigroup_eq_fourierMultiplierCLM (t : ℝ≥0) :
    heatSemigroup E F t =
      fourierMultiplierCLM F fun ξ ↦ ((rexp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℝ) : ℂ) :=
  (rfl)

variable (E F) in
/-- At time `0` the heat semigroup is the identity. -/
@[simp]
theorem heatSemigroup_zero : heatSemigroup E F 0 = ContinuousLinearMap.id ℂ _ := by
  ext u
  simp [heatSemigroup]

/-- **The semigroup law** `e^{tΔ} e^{sΔ} = e^{(s+t)Δ}` on tempered distributions. -/
@[simp]
theorem heatSemigroup_heatSemigroup_apply (s t : ℝ≥0) (u : 𝓢'(E, F)) :
    heatSemigroup E F t (heatSemigroup E F s u) = heatSemigroup E F (s + t) u := by
  rw [heatSemigroup, heatSemigroup, heatSemigroup,
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      (by exact Complex.hasTemperateGrowth_ofReal.comp
            (Function.hasTemperateGrowth_exp_neg_mul_norm_sq (by positivity)))
      (by exact Complex.hasTemperateGrowth_ofReal.comp
            (Function.hasTemperateGrowth_exp_neg_mul_norm_sq (by positivity)))]
  congr 2
  funext ξ
  rw [Pi.mul_apply, ← Complex.ofReal_mul, ← Real.exp_add, NNReal.coe_add]
  ring_nf

/-- The semigroup law `e^{tΔ} ∘ e^{sΔ} = e^{(s+t)Δ}` as an identity of operators. -/
theorem heatSemigroup_compL_heatSemigroup (s t : ℝ≥0) :
    heatSemigroup E F t ∘L heatSemigroup E F s = heatSemigroup E F (s + t) := by
  ext1 u
  exact heatSemigroup_heatSemigroup_apply s t u

/-- At a positive time the heat semigroup is the Fourier multiplier with the Schwartz symbol
`SchwartzMap.gaussian` at `b = 4π² t`. -/
private theorem heatSemigroup_eq_fourierMultiplierCLM_gaussian {t : ℝ≥0}
    (hb : 0 < ((4 * π ^ 2 * t : ℝ) : ℂ).re) :
    heatSemigroup E F t = fourierMultiplierCLM F ⇑(SchwartzMap.gaussian (V := E) hb) := by
  rw [heatSemigroup, SchwartzMap.coe_gaussian_ofReal]

variable [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The heat semigroup is convolution with the heat kernel.** At a time `t > 0`, the heat
semigroup sends the tempered distribution of `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, to an `Lᵖ` function `g`
equal almost everywhere to `K_t ⋆ f`, with `‖g‖_p ≤ ‖f‖_p`. -/
theorem exists_heatSemigroup_eq_and_ae_eq_convolution {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E), heatSemigroup E F t (f : 𝓢'(E, F)) = g ∧
      g =ᵐ[volume] heatKernel t ⋆ (f : E → F) ∧ ‖g‖ ≤ ‖f‖ := by
  have ht' : (0 : ℝ) < t := by positivity
  have hb : 0 < ((4 * π ^ 2 * t : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  have hK : 𝓕⁻ (SchwartzMap.gaussian (V := E) hb : E → ℂ) = fun x ↦ (heatKernel t x : ℂ) := by
    rw [SchwartzMap.coe_gaussian_ofReal, fourierInv_exp_neg_mul_norm_sq ht']
  obtain ⟨g, hg, hgK, hgn⟩ := exists_fourierMultiplierCLM_toTemperedDistribution_eq
    (SchwartzMap.gaussian (V := E) hb) f (q := p) (r := 1) le_rfl (by rw [inv_one, add_comm])
  refine ⟨g, by rw [heatSemigroup_eq_fourierMultiplierCLM_gaussian hb, hg], ?_, ?_⟩
  · refine hgK.trans (.of_forall fun x ↦ ?_)
    rw [hK]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, Complex.coe_smul]
  · -- The kernel `K_t` is nonnegative with mass one, so its `L¹` norm is one.
    have h1 : eLpNorm (𝓕⁻ (SchwartzMap.gaussian (V := E) hb : E → ℂ)) 1 volume = 1 := by
      have hKi : Integrable (fun x : E ↦ (heatKernel t x : ℂ)) :=
        (integrable_heatKernel ht').ofReal
      rw [hK, eLpNorm_one_eq_lintegral_eNorm hKi.aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_eNorm hKi]
      simp_rw [Complex.norm_real, Real.norm_of_nonneg (heatKernel_pos ht' _).le,
        integral_heatKernel ht', ENNReal.ofReal_one]
    rwa [h1, ENNReal.toReal_one, one_mul] at hgn

/-- **The heat semigroup is a contraction on every `Lᵖ`.** For `1 ≤ p ≤ ∞`, `t ≥ 0` and
`f ∈ Lᵖ`, the tempered distribution `e^{tΔ} f` is an `Lᵖ` function `g` with `‖g‖_p ≤ ‖f‖_p`. -/
theorem exists_heatSemigroup_eq_and_norm_le (t : ℝ≥0) (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E), heatSemigroup E F t (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ ‖f‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨f, by simp, le_rfl⟩
  obtain ⟨g, hg, -, hgn⟩ := exists_heatSemigroup_eq_and_ae_eq_convolution ht f
  exact ⟨g, hg, hgn⟩

/-- **Agreement with the heat semigroup on `Lᵖ`.** For `1 ≤ p < ∞`, the heat semigroup on
tempered distributions extends the heat semigroup `TauCeti.heatSemigroup` on `Lᵖ`. -/
theorem heatSemigroup_toTemperedDistribution (hp : p ≠ ∞) (t : ℝ≥0)
    (f : Lp F p (volume : Measure E)) :
    heatSemigroup E F t (f : 𝓢'(E, F)) =
      ((TauCeti.heatSemigroup hp t f : Lp F p (volume : Measure E)) : 𝓢'(E, F)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  obtain ⟨g, hg, hgK, -⟩ := exists_heatSemigroup_eq_and_ae_eq_convolution ht f
  rw [hg]
  congr 1
  exact Lp.ext (hgK.trans (TauCeti.heatSemigroup_ae_eq_convolution_coeFn hp ht f).symm)

end TemperedDistribution
