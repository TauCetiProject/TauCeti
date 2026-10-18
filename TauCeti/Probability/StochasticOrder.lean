/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile.Basic

/-!
# Stochastic comparison of real probability laws

One real probability law is stochastically below another when its cumulative distribution
function is everywhere larger. This file keeps that comparison as a pointwise inequality rather
than introducing a second order on measures. It uses the equivalence between that comparison and
the opposite pointwise comparison of the two quantile functions on `(0, 1)`.

The equivalence has a concrete coupling interpretation. The monotone quantile coupling reads both
quantiles from the same uniform variable, and is concentrated on ordered pairs exactly when the cdf
comparison holds. Conversely, any coupling concentrated on ordered pairs implies the corresponding
cdf inequality. Thus the quantile construction supplies a canonical ordered coupling without a new
coupling structure.

The comparison is preserved by nondecreasing maps. Later distribution-specific monotonicity
results can therefore work either with cdfs, quantiles, or explicit ordered couplings according to
which form their construction naturally provides.

## Main results

* `TauCeti.IsCoupling.cdf_le_of_ae_fst_le_snd` — every almost surely ordered coupling implies the
  cdf comparison;
* `MeasureTheory.Measure.ae_fst_le_snd_quantileCoupling_iff` — the monotone quantile coupling is
  ordered exactly under the cdf comparison;
* `MeasureTheory.Measure.cdf_le_iff_exists_ae_le_coupling` — cdf comparison is equivalent to the
  existence of an ordered coupling;
* `MeasureTheory.Measure.cdf_map_le_cdf_map_of_monotone` — stochastic comparison is preserved by
  measurable nondecreasing maps.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.IsCoupling

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-- **An ordered coupling implies cdf comparison.** If a coupling of `μ` and `ν` is concentrated
on pairs `(x, y)` with `x ≤ y`, then `cdf ν a ≤ cdf μ a` for every threshold `a`.

Indeed, whenever the second coordinate is at most `a`, so is the first coordinate. The marginal
identities of the coupling then compare the two lower-half-line probabilities. -/
theorem cdf_le_of_ae_fst_le_snd [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : TauCeti.IsCoupling π μ ν) (hle : ∀ᵐ z ∂π, z.1 ≤ z.2) (a : ℝ) :
    cdf ν a ≤ cdf μ a := by
  rw [← ENNReal.ofReal_le_ofReal_iff (cdf_nonneg μ a), ofReal_cdf, ofReal_cdf,
    ← hπ.measure_univ_prod measurableSet_Iic, ← hπ.measure_prod_univ measurableSet_Iic]
  exact measure_mono_ae <| hle.mono fun z hz hza => ⟨hz.trans hza.2, mem_univ z.2⟩

end TauCeti.IsCoupling

namespace MeasureTheory.Measure

variable {μ ν : Measure ℝ}

/-- **The monotone coupling is ordered exactly under cdf comparison.** The common-uniform
quantile coupling of `μ` and `ν` is concentrated on `{(x, y) | x ≤ y}` if and only if
`cdf ν ≤ cdf μ` pointwise. -/
theorem ae_fst_le_snd_quantileCoupling_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ᵐ z ∂μ.quantileCoupling ν, z.1 ≤ z.2) ↔ ∀ x, cdf ν x ≤ cdf μ x := by
  constructor
  · exact fun h => (μ.isCoupling_quantileCoupling ν).cdf_le_of_ae_fst_le_snd h
  · intro h
    rw [quantileCoupling_def,
      ae_map_iff (by fun_prop) (measurableSet_le measurable_fst measurable_snd)]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact cdf_le_iff_quantile_le.mp h t ht

/-- **Ordered-coupling characterization of cdf comparison.** For real probability laws,
`cdf ν ≤ cdf μ` pointwise if and only if some coupling of `μ` and `ν` is almost surely ordered.
The forward implication is witnessed by the monotone quantile coupling. -/
theorem cdf_le_iff_exists_ae_le_coupling [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ x, cdf ν x ≤ cdf μ x) ↔
      ∃ π : Measure (ℝ × ℝ), TauCeti.IsCoupling π μ ν ∧ ∀ᵐ z ∂π, z.1 ≤ z.2 := by
  constructor
  · intro h
    exact ⟨μ.quantileCoupling ν, μ.isCoupling_quantileCoupling ν,
      ae_fst_le_snd_quantileCoupling_iff.mpr h⟩
  · rintro ⟨π, hπ, hle⟩
    exact hπ.cdf_le_of_ae_fst_le_snd hle

/-- Stochastic comparison is preserved by a nondecreasing real map. If
`cdf ν ≤ cdf μ`, then the image of `μ` remains stochastically below the image of `ν`.
Monotonicity alone suffices; neither continuity nor strict monotonicity is required. -/
theorem cdf_map_le_cdf_map_of_monotone [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hmono : Monotone f) (h : ∀ x, cdf ν x ≤ cdf μ x) :
    ∀ x, cdf (ν.map f) x ≤ cdf (μ.map f) x := by
  let π := (μ.quantileCoupling ν).map (Prod.map f f)
  have hπ : TauCeti.IsCoupling π (μ.map f) (ν.map f) :=
    (μ.isCoupling_quantileCoupling ν).map hmono.measurable hmono.measurable
  apply hπ.cdf_le_of_ae_fst_le_snd
  dsimp only [π]
  rw [ae_map_iff (hmono.measurable.prodMap hmono.measurable).aemeasurable
    (measurableSet_le measurable_fst measurable_snd)]
  filter_upwards [ae_fst_le_snd_quantileCoupling_iff.mpr h] with z hz
  exact hmono hz

end MeasureTheory.Measure
