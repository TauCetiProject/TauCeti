/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile.Basic

/-!
# First-order stochastic comparison of real probability laws

For probability laws on the real line, reversed pointwise comparison of cumulative distribution
functions is equivalent to pointwise comparison of all interior quantiles. The common-uniform
quantile coupling realizes this comparison almost surely. Conversely, any coupling supported on
ordered pairs forces the corresponding cumulative-distribution comparison.

The results are stated directly as inequalities between cdfs and quantiles, rather than through a
new relation on measures. This keeps the API compatible with the existing pointwise order on
measures while still providing the characteristic forms used in stochastic-order arguments.

## Main results

* `TauCeti.IsCoupling.cdf_le_of_ae_fst_le_snd` shows that any coupling concentrated on ordered
  pairs forces the reversed cdf inequality.
* `MeasureTheory.Measure.exists_isCoupling_ae_fst_le_snd_iff_cdf_le` packages the coupling
  characterization.
* `ProbabilityTheory.HasLaw.cdf_le_of_ae_le` gives the random-variable form of the converse.

## References

* M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer, 2007, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace IsCoupling

/-- Any coupling of two real probability laws that is almost surely supported on ordered pairs
forces the reversed pointwise cdf inequality. -/
theorem cdf_le_of_ae_fst_le_snd {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν)
    (h : ∀ᵐ z ∂π, z.1 ≤ z.2) (x : ℝ) : cdf ν x ≤ cdf μ x := by
  let _ : IsProbabilityMeasure ν := hπ.isProbabilityMeasure_right
  let _ : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hsubset : (univ ×ˢ Iic x) ≤ᵐ[π] (Iic x ×ˢ univ) := by
    filter_upwards [h] with z hz hzx
    exact ⟨hz.trans hzx.2, mem_univ _⟩
  rw [cdf_eq_real, cdf_eq_real, Measure.real, Measure.real,
    ← hπ.measure_univ_prod measurableSet_Iic, ← hπ.measure_prod_univ measurableSet_Iic]
  exact ENNReal.toReal_mono (measure_ne_top π _) (measure_mono_ae hsubset)

end IsCoupling

end TauCeti

namespace MeasureTheory.Measure

/-- Two real probability laws have reversed cdfs exactly when they admit a coupling concentrated
on ordered pairs. The forward implication is witnessed by the common-uniform quantile coupling. -/
theorem exists_isCoupling_ae_fst_le_snd_iff_cdf_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∃ π : Measure (ℝ × ℝ), TauCeti.IsCoupling π μ ν ∧ ∀ᵐ z ∂π, z.1 ≤ z.2) ↔
      ∀ x, cdf ν x ≤ cdf μ x := by
  constructor
  · rintro ⟨π, hπ, hle⟩ x
    exact hπ.cdf_le_of_ae_fst_le_snd hle x
  · intro h
    exact ⟨μ.quantileCoupling ν, μ.isCoupling_quantileCoupling ν,
      μ.ae_fst_le_snd_quantileCoupling ν h⟩

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

/-- If two real random variables on the same probability space are almost surely ordered, then
their laws have the corresponding reversed cdf inequality. No independence is required. -/
theorem cdf_le_of_ae_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} {μ ν : Measure ℝ} (hX : HasLaw X μ P)
    (hY : HasLaw Y ν P) (h : ∀ᵐ ω ∂P, X ω ≤ Y ω) (x : ℝ) : cdf ν x ≤ cdf μ x := by
  let _ : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.1 inferInstance
  let _ : IsProbabilityMeasure ν := hY.isProbabilityMeasure_iff.1 inferInstance
  let π := P.map fun ω ↦ (X ω, Y ω)
  have hπdef : π = P.map fun ω ↦ (X ω, Y ω) := rfl
  have hπ : TauCeti.IsCoupling π μ ν := by
    constructor
    · rw [hπdef]
      exact (Measure.fst_map_prodMk₀ hX.aemeasurable hY.aemeasurable).trans hX.map_eq
    · rw [hπdef]
      exact (Measure.snd_map_prodMk₀ hX.aemeasurable hY.aemeasurable).trans hY.map_eq
  have hπle : ∀ᵐ z ∂π, z.1 ≤ z.2 := by
    rw [hπdef]
    exact (ae_map_iff (hX.aemeasurable.prodMk hY.aemeasurable)
      (measurableSet_le measurable_fst measurable_snd)).2 h
  exact hπ.cdf_le_of_ae_fst_le_snd hπle x

end ProbabilityTheory.HasLaw
