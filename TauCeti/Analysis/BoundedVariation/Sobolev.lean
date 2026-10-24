/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.FunctionalSpaces.SobolevInequality
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# The Sobolev inequality for functions of bounded variation

Let `E` be a real inner product space of finite dimension `n ≥ 2` with an additive Haar measure
`μ`, and let `p = n / (n - 1)`. This file proves the **Gagliardo–Nirenberg–Sobolev inequality for
functions of bounded variation**: every integrable `u : E → ℝ` satisfies

`‖u‖_p ≤ C |Du|(E)`,

where `|Du|(E)` is the variational total variation `TauCeti.totalVariationOn μ ⊤ u`, finite or
infinite, and `C = MeasureTheory.eLpNormLESNormFDerivOneConst μ p` is the constant of Mathlib's
inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one` for compactly supported `C¹` functions.
No compact support and no differentiability are assumed. Applied to indicators, it gives the
nonsharp **isoperimetric inequality** `μ(s) ^ (1 - 1/n) ≤ C P(s; E)` for every null-measurable
set of finite measure; finiteness of the perimeter is not assumed either.

The proof mollifies `u`. The mollifications `ρ_ε ⋆ u` are smooth and integrable, so they satisfy
the inequality `‖ρ_ε ⋆ u‖_p ≤ C ‖D(ρ_ε ⋆ u)‖₁` for integrable `C¹` functions
(`TauCeti.eLpNorm_le_eLpNorm_fderiv_one_of_integrable`). For a smooth function `‖Dv‖₁` is the
total variation `|Dv|(E)`, and `|D(ρ_ε ⋆ u)|(E) ≤ |Du|(E)` by the convolution estimate
`ContDiffBump.totalVariationOn_normed_convolution_le`. The mollifications converge to `u` in `L¹`,
so Fatou's lemma along an almost everywhere convergent subsequence passes the inequality to `u`.

## Main results

* `TauCeti.eLpNorm_le_totalVariationOn`: the Sobolev inequality `‖u‖_p ≤ C |Du|(E)` for every
  integrable `u`.
* `TauCeti.measure_rpow_le_perimeter`: the isoperimetric inequality `μ(s) ^ (1/p) ≤ C P(s; E)`
  for every null-measurable set `s` of finite measure.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.47.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.6.1,
  Theorem 1.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 12.37.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Module Set TopologicalSpace ContinuousLinearMap
open scoped ENNReal NNReal Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0}
  {u : E → ℝ}

/-- **The Sobolev inequality for functions of bounded variation.** Let `E` have dimension
`n ≥ 2` and let `p = n / (n - 1)`. Every integrable `u : E → ℝ` satisfies `‖u‖_p ≤ C |Du|(E)`,
where `|Du|(E)` is the total variation of `u` on the whole space, finite or infinite, and `C` is
the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the `C¹` Gagliardo–Nirenberg–
Sobolev inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`. -/
theorem eLpNorm_le_totalVariationOn (hu : Integrable u μ)
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p * totalVariationOn μ ⊤ u := by
  set C := eLpNormLESNormFDerivOneConst μ p
  -- Mollify `u` with normalized bumps of outer radius `1 / (n + 1)`.
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set v : ℕ → E → ℝ := fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] u
  have hsmooth (n : ℕ) : ContDiff ℝ 1 (v n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hu.locallyIntegrable
  -- Each mollification has variation, hence `∫ ‖Dv‖`, at most `|Du|(E)`.
  have hvar (n : ℕ) : ∫⁻ x, ‖fderiv ℝ (v n) x‖ₑ ∂μ ≤ totalVariationOn μ ⊤ u := by
    have := (hsmooth n).locallyLipschitz.locallyLipschitzOn
      |>.totalVariationOn_eq_setLIntegral_enorm_fderiv (μ := μ) (Ω := ⊤)
    rw [Opens.coe_top, Measure.restrict_univ] at this
    rw [← this]
    exact (φ n).totalVariationOn_normed_convolution_le (hu.locallyIntegrable.locallyIntegrableOn _)
      fun _ _ => subset_univ _
  have hbound (n : ℕ) : eLpNorm (v n) p μ ≤ C * totalVariationOn μ ⊤ u := by
    refine (eLpNorm_le_eLpNorm_fderiv_one_of_integrable μ (hsmooth n)
      ((φ n).integrable_normed.integrable_convolution _ hu) hp).trans ?_
    rw [eLpNorm_one_eq_lintegral_enorm
      ((hsmooth n).continuous_fderiv one_ne_zero).aestronglyMeasurable]
    exact mul_le_mul_right (hvar n) _
  -- The mollifications converge to `u` in `L¹`; Fatou's lemma along an almost everywhere
  -- convergent subsequence concludes.
  have hlim := tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hφ
    (memLp_one_iff_integrable.2 hu)
  obtain ⟨ns, -, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hlim).exists_seq_tendsto_ae
  exact (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun n => (hsmooth (ns n)).continuous.aestronglyMeasurable) u hu.aestronglyMeasurable
    hae).trans (liminf_le_of_frequently_le' (.of_forall fun n => hbound (ns n)))

/-- **The nonsharp isoperimetric inequality.** Let `E` have dimension `n ≥ 2` and let
`p = n / (n - 1)`. Every null-measurable set `s` of finite measure satisfies
`μ(s) ^ (1/p) ≤ C P(s; E)`, where `1/p = 1 - 1/n`, `P(s; E)` is the perimeter of `s` in the whole
space, finite or infinite, and `C` is the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p`
of the Gagliardo–Nirenberg–Sobolev inequality. -/
theorem measure_rpow_le_perimeter {s : Set E} (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ∞)
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    μ s ^ (p : ℝ)⁻¹ ≤ eLpNormLESNormFDerivOneConst μ p * perimeter μ ⊤ s := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.symm.pos.ne'
  have hint : Integrable (s.indicator (1 : E → ℝ)) μ :=
    (integrable_indicator_iff₀ hs).2 (integrableOn_const hμs)
  simpa [perimeter_def, eLpNorm_indicator_const hs hp0 ENNReal.coe_ne_top, Pi.one_def] using
    eLpNorm_le_totalVariationOn hint hp

end TauCeti
