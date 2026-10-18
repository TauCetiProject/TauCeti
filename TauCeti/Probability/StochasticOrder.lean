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

* `MeasureTheory.Measure.cdf_le_iff_quantile_le` characterizes reversed cdf comparison by
  interior quantile comparison.
* `MeasureTheory.Measure.ae_fst_le_snd_quantileCoupling` shows that the common-uniform coupling is
  ordered whenever the cdfs are ordered.
* `TauCeti.IsCoupling.cdf_le_of_ae_fst_le_snd` proves the converse for an arbitrary coupling.
* `MeasureTheory.Measure.exists_isCoupling_ae_fst_le_snd_iff_cdf_le` packages the coupling
  characterization.
* `ProbabilityTheory.HasLaw.cdf_le_of_ae_le` gives the random-variable form of the converse.

## References

* M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer, 2007, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

/-- Reversed pointwise comparison of the cdfs of two real probability laws is equivalent to
pointwise comparison of their quantiles at every level strictly between zero and one. -/
theorem cdf_le_iff_quantile_le (μ ν : Measure ℝ) :
    (∀ x, cdf ν x ≤ cdf μ x) ↔
      ∀ u, 0 < u → u < 1 → μ.quantile u ≤ ν.quantile u := by
  constructor
  · intro hcdf u hu0 hu1
    rw [quantile_le_iff μ hu0 hu1]
    exact (le_cdf_quantile ν hu1).trans (hcdf _)
  · intro hquant x
    by_contra hle
    have hlt : cdf μ x < cdf ν x := lt_of_not_ge hle
    let u := (cdf μ x + cdf ν x) / 2
    have hu0 : 0 < u := by
      dsimp [u]
      linarith [cdf_nonneg μ x]
    have hu1 : u < 1 := by
      dsimp [u]
      linarith [cdf_le_one ν x]
    have hμu : cdf μ x < u := by
      dsimp [u]
      linarith
    have huν : u ≤ cdf ν x := by
      dsimp [u]
      linarith
    have hνq : ν.quantile u ≤ x := (quantile_le_iff ν hu0 hu1).2 huν
    have hμq : μ.quantile u ≤ x := (hquant u hu0 hu1).trans hνq
    exact (not_le_of_gt hμu) ((quantile_le_iff μ hu0 hu1).1 hμq)

/-- If the cdfs are ordered, the common-uniform quantile coupling is concentrated on ordered
pairs. Thus the stochastic comparison is realized by random variables satisfying `X ≤ Y` almost
surely. -/
theorem ae_fst_le_snd_quantileCoupling (μ ν : Measure ℝ) (h : ∀ x, cdf ν x ≤ cdf μ x) :
  ∀ᵐ z ∂μ.quantileCoupling ν, z.1 ≤ z.2 := by
  rw [quantileCoupling_def]
  refine (ae_map_iff (by fun_prop) (measurableSet_le measurable_fst measurable_snd)).2 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact (cdf_le_iff_quantile_le μ ν).1 h u hu.1 hu.2

end MeasureTheory.Measure

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
