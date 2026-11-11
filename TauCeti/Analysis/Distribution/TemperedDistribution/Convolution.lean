/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.FourierMultiplier
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution

/-!
# Fourier multipliers with Schwartz symbols on `Lᵖ` functions

Let `σ` be a Schwartz function on a finite-dimensional real inner product space `E`. The Fourier
multiplier `T_σ u = 𝓕⁻ (σ • 𝓕 u)` on tempered distributions
(`TemperedDistribution.fourierMultiplierCLM`) acts on the tempered distribution of an `Lᵖ`
function `f`, for any `1 ≤ p ≤ ∞`, as convolution with the Schwartz kernel `𝓕⁻ σ`:

`T_σ f = 𝓕⁻ σ ⋆ f`, where `(𝓕⁻ σ ⋆ f) x = ∫ y, 𝓕⁻ σ (x - y) • f y`.

Together with Young's convolution inequality this shows that `T_σ` maps `Lᵖ` to `Lᵠ` for every
`q ≥ p`, with `‖T_σ f‖_q ≤ ‖𝓕⁻ σ‖_r ‖f‖_p` whenever `1/p + 1/r = 1 + 1/q`.

The identity is proved by pairing with a test function `φ`: by definition
`T_σ f (φ) = ∫ 𝓕 (σ • 𝓕⁻ φ) • f`, the convolution theorem for Schwartz functions writes
`𝓕 (σ • 𝓕⁻ φ) y = ∫ x, 𝓕 σ (y - x) * φ x`, and Fubini's theorem exchanges the two integrals. The
double integral converges absolutely by Hölder's inequality in `y` and Young's inequality for the
inner integral, so no restriction on `p` is needed. This covers `p = ∞`, where the Schwartz
functions are not dense and the multiplier cannot be obtained by extension from them. For
`p = 2` the same kernel represents the `L²` multiplier `MeasureTheory.Lp.fourierMultiplierCLM`
(`SchwartzMap.coeFn_fourierMultiplierCLM_toLp`).

This is the form in which frequency-localized functions are handled: a function whose Fourier
transform is supported in a ball is reproduced by a multiplier whose symbol is a bump function
equal to one on that ball, so that it is a convolution with a fixed Schwartz kernel. Bernstein's
inequalities are derived this way.

## Main declarations

* `TemperedDistribution.fourierMultiplierCLM_toTemperedDistribution_apply`: the pairing of `T_σ f`
  with a test function is the pairing of the convolution `𝓕⁻ σ ⋆ f`.
* `TemperedDistribution.exists_fourierMultiplierCLM_toTemperedDistribution_eq`: `T_σ f` is the
  `Lᵠ` function `𝓕⁻ σ ⋆ f`, with `‖T_σ f‖_q ≤ ‖𝓕⁻ σ‖_r ‖f‖_p`.
* `TemperedDistribution.exists_fourierMultiplierCLM_eq_and_norm_le`: the case `q = p`, `r = 1`,
  `‖T_σ f‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Sections 2.3 and 2.5.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.1.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory SchwartzMap ContinuousLinearMap
open scoped ENNReal FourierTransform SchwartzMap Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

omit [CompleteSpace F] in
/-- The integrand `(y, x) ↦ (𝓕 σ (y - x) * φ x) • f y` of the pairing of `T_σ f` with `φ` is
integrable on `E × E`: its integral in `x` is `‖f y‖` times the convolution of `‖φ‖` with
`‖𝓕 σ‖`, which lies in the conjugate space of `Lᵖ` by Young's inequality. -/
private theorem integrable_fourier_sub_mul_smul (σ φ : 𝓢(E, ℂ)) (f : Lp F p (volume : Measure E)) :
    Integrable (Function.uncurry fun y x ↦ (𝓕 σ (y - x) * φ x) • f y)
      ((volume : Measure E).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun y x ↦ (𝓕 σ (y - x) * φ x) • f y)
      ((volume : Measure E).prod volume) :=
    (((𝓕 σ).continuous.comp (continuous_fst.sub continuous_snd)).mul
      (φ.continuous.comp continuous_snd)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f).comp_fst
  refine ⟨hmeas, ?_⟩
  set H : E → ℝ≥0∞ := (fun x ↦ ‖φ x‖ₑ) ⋆ₗ[volume] fun x ↦ ‖𝓕 σ x‖ₑ
  have hinner : ∀ y, ∫⁻ x, ‖(𝓕 σ (y - x) * φ x) • f y‖ₑ = ‖f y‖ₑ * H y := fun y ↦ by
    simp only [H, lconvolution_def]
    rw [← lintegral_const_mul' _ _ enorm_ne_top]
    refine lintegral_congr fun x ↦ ?_
    rw [enorm_smul, enorm_mul, neg_add_eq_sub]
    ring
  rw [HasFiniteIntegral, lintegral_prod _ hmeas.enorm]
  simp only [Function.uncurry_apply_pair, hinner]
  -- Hölder's inequality with the conjugate exponent `p'` of `p`, then Young's inequality
  -- `‖H‖_{p'} ≤ ‖φ‖_{p'} ‖𝓕 σ‖_1`.
  set p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hpp' : p.HolderConjugate p' := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  have hp' : 1 ≤ p' := ENNReal.one_le_inv.2 tsub_le_self
  have hHm : AEMeasurable H volume :=
    aemeasurable_lconvolution φ.continuous.enorm.aemeasurable
      (𝓕 σ).continuous.enorm.aemeasurable
  have hfH : AEStronglyMeasurable (fun y ↦ ‖f y‖ₑ * H y) volume :=
    ((Lp.aestronglyMeasurable f).enorm.mul hHm).aestronglyMeasurable
  calc ∫⁻ y, ‖f y‖ₑ * H y
      = eLpNorm (fun y ↦ ‖f y‖ₑ * H y) 1 volume := by
        rw [eLpNorm_one_eq_lintegral_enorm hfH]
        simp
    _ ≤ 1 * eLpNorm f p volume * eLpNorm H p' volume :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (fun v h ↦ ‖v‖ₑ * h) 1
          (fun hf hH ↦ (hf.enorm.mul hH.aemeasurable).aestronglyMeasurable)
          (Lp.aestronglyMeasurable f) hHm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ ↦ by simp)
    _ ≤ 1 * eLpNorm f p volume *
          (eLpNorm (fun x ↦ ‖φ x‖ₑ) p' volume * eLpNorm (fun x ↦ ‖𝓕 σ x‖ₑ) 1 volume) := by
        gcongr
        exact eLpNorm_lconvolution_le hp' le_rfl (by rw [inv_one, add_comm])
          φ.continuous.enorm.aemeasurable (𝓕 σ).continuous.enorm.aemeasurable
    _ < ∞ := by
        rw [eLpNorm_enorm _ φ.continuous.aestronglyMeasurable,
          eLpNorm_enorm _ (𝓕 σ).continuous.aestronglyMeasurable, one_mul]
        exact ENNReal.mul_lt_top (Lp.eLpNorm_lt_top f)
          (ENNReal.mul_lt_top (φ.eLpNorm_lt_top p' volume) ((𝓕 σ).eLpNorm_lt_top 1 volume))

/-- **A Fourier multiplier with a Schwartz symbol acts on `Lᵖ` by convolution.** For a Schwartz
symbol `σ` and `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, the tempered distribution `T_σ f = 𝓕⁻ (σ • 𝓕 f)` pairs with
every test function `φ` as the convolution `𝓕⁻ σ ⋆ f` does. -/
theorem fourierMultiplierCLM_toTemperedDistribution_apply (σ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F σ (f : 𝓢'(E, F)) φ =
      ∫ x, φ x • (𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F)) x := by
  rw [fourierMultiplierCLM_apply_apply, Lp.toTemperedDistribution_apply]
  -- The convolution theorem: `𝓕 (σ • 𝓕⁻ φ) y = ∫ x, 𝓕 σ (y - x) * φ x`.
  have hΦ : ∀ y, 𝓕 (SchwartzMap.smulLeftCLM ℂ (σ : E → ℂ) (𝓕⁻ φ)) y =
      ∫ x, 𝓕 σ (y - x) * φ x := fun y ↦ by
    rw [SchwartzMap.fourier_smulLeftCLM_apply (F := ℂ), FourierTransform.fourier_fourierInv_eq,
      ← integral_sub_left_eq_self _ volume y]
    simp [sub_sub_cancel]
  have hconv : ∀ x, (𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F)) x =
      ∫ y, 𝓕 σ (y - x) • f y := fun x ↦ by
    rw [convolution_eq_swap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [Real.fourierInv_eq_fourier_neg, neg_sub, SchwartzMap.fourier_coe, lsmul_apply]
  simp_rw [hΦ, hconv]
  calc ∫ y, (∫ x, 𝓕 σ (y - x) * φ x) • f y
      = ∫ y, ∫ x, (𝓕 σ (y - x) * φ x) • f y := by
        simp_rw [integral_smul_const]
    _ = ∫ x, ∫ y, (𝓕 σ (y - x) * φ x) • f y :=
        integral_integral_swap (integrable_fourier_sub_mul_smul σ φ f)
    _ = ∫ x, φ x • ∫ y, 𝓕 σ (y - x) • f y := by
        simp_rw [← integral_smul, mul_comm (𝓕 σ _), mul_smul]

/-- **A Fourier multiplier with a Schwartz symbol maps `Lᵖ` to `Lᵠ`.** For a Schwartz symbol `σ`,
`f ∈ Lᵖ` and exponents with `1 ≤ r` and `1/p + 1/r = 1 + 1/q`, the tempered distribution
`T_σ f = 𝓕⁻ (σ • 𝓕 f)` is the `Lᵠ` function `𝓕⁻ σ ⋆ f`, and
`‖T_σ f‖_q ≤ ‖𝓕⁻ σ‖_r ‖f‖_p`. -/
theorem exists_fourierMultiplierCLM_toTemperedDistribution_eq (σ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) {q r : ℝ≥0∞} [Fact (1 ≤ q)] (hr : 1 ≤ r)
    (hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹) :
    ∃ g : Lp F q (volume : Measure E),
      fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g ∧
      g =ᵐ[volume] 𝓕⁻ (σ : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F) ∧
      ‖g‖ ≤ (eLpNorm (𝓕⁻ (σ : E → ℂ)) r volume).toReal * ‖f‖ := by
  -- Work with the Schwartz kernel `𝓕⁻ σ`, which is continuous and lies in every `Lʳ`.
  rw [← SchwartzMap.fourierInv_coe]
  set K : 𝓢(E, ℂ) := 𝓕⁻ σ
  set h := (K : E → ℂ) ⋆[lsmul ℂ ℂ] (f : E → F)
  have hL : ‖lsmul ℂ ℂ (E := F)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 opNorm_lsmul_le
  have hbound : eLpNorm h q volume ≤ eLpNorm K r volume * eLpNorm f p volume :=
    calc eLpNorm h q volume
        ≤ ‖lsmul ℂ ℂ (E := F)‖ₑ * eLpNorm K r volume * eLpNorm f p volume :=
          eLpNorm_convolution_le_of_inv_add_inv_eq _ hr hp.out (by rw [add_comm, hpqr])
            K.continuous.aestronglyMeasurable (Lp.aestronglyMeasurable f)
      _ ≤ eLpNorm K r volume * eLpNorm f p volume := by
          rw [mul_assoc]
          exact mul_le_of_le_one_left (zero_le) hL
  have hfin : eLpNorm K r volume * eLpNorm f p volume ≠ ∞ :=
    ENNReal.mul_ne_top (K.eLpNorm_lt_top r volume).ne (Lp.eLpNorm_lt_top f).ne
  have hmem : MemLp h q volume := memLp_iff.2 (lt_of_le_of_lt hbound (Ne.lt_top hfin))
  refine ⟨hmem.toLp h, ?_, hmem.coeFn_toLp, ?_⟩
  · ext φ
    rw [fourierMultiplierCLM_toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
      ← SchwartzMap.fourierInv_coe]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
  · rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hfin hbound

/-- **`Lᵖ` bound for a multiplier with Schwartz symbol.** For `1 ≤ p ≤ ∞`, the Fourier multiplier
with a Schwartz symbol `σ` maps every `f ∈ Lᵖ` to a function `g ∈ Lᵖ` with
`‖g‖_p ≤ ‖𝓕⁻ σ‖₁ ‖f‖_p`. This is the case `q = p`, `r = 1` of
`TemperedDistribution.exists_fourierMultiplierCLM_toTemperedDistribution_eq`. -/
theorem exists_fourierMultiplierCLM_eq_and_norm_le (σ : 𝓢(E, ℂ))
    (f : Lp F p (volume : Measure E)) :
    ∃ g : Lp F p (volume : Measure E), fourierMultiplierCLM F σ (f : 𝓢'(E, F)) = g ∧
      ‖g‖ ≤ (∫ x, ‖𝓕⁻ (σ : E → ℂ) x‖) * ‖f‖ := by
  obtain ⟨g, hg, -, hgf⟩ :=
    exists_fourierMultiplierCLM_toTemperedDistribution_eq σ f (q := p) (r := 1) le_rfl
      (by rw [inv_one, add_comm])
  have hK : AEStronglyMeasurable (𝓕⁻ (σ : E → ℂ)) volume := by
    rw [← SchwartzMap.fourierInv_coe]
    exact (𝓕⁻ σ).continuous.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hK, ← integral_norm_eq_lintegral_enorm hK] at hgf
  exact ⟨g, hg, hgf⟩

end TemperedDistribution
