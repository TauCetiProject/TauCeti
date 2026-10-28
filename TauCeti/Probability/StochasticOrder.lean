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
* `MeasureTheory.Measure.cdf_map_le_cdf_map_of_monotone` shows that nondecreasing images preserve
  the comparison.
* `MeasureTheory.Measure.cdf_conv_le_cdf_conv` shows that convolution preserves the comparison in
  both arguments.
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

/-- Reversed pointwise cdf comparison is reflexive. -/
theorem cdf_le_refl (μ : Measure ℝ) : ∀ x, cdf μ x ≤ cdf μ x := fun _ ↦ le_rfl

/-- Reversed pointwise cdf comparison is transitive. -/
theorem cdf_le_trans {μ ν ρ : Measure ℝ} (hμν : ∀ x, cdf ν x ≤ cdf μ x)
    (hνρ : ∀ x, cdf ρ x ≤ cdf ν x) : ∀ x, cdf ρ x ≤ cdf μ x :=
  fun x ↦ (hνρ x).trans (hμν x)

/-- Two real probability laws that compare in both directions by their cdfs are equal. -/
theorem eq_of_cdf_le_cdf_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : ∀ x, cdf ν x ≤ cdf μ x)
    (hνμ : ∀ x, cdf μ x ≤ cdf ν x) : μ = ν := by
  apply Measure.eq_of_cdf
  ext x
  exact (hνμ x).antisymm (hμν x)

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

namespace MeasureTheory.Measure

/-- A nondecreasing image preserves reversed pointwise cdf comparison of probability laws. -/
theorem cdf_map_le_cdf_map_of_monotone {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : ℝ → ℝ} (hg : Monotone g)
    (hμν : ∀ x, cdf ν x ≤ cdf μ x) :
    ∀ x, cdf (ν.map g) x ≤ cdf (μ.map g) x := by
  let π := μ.quantileCoupling ν
  have hπ : TauCeti.IsCoupling π μ ν := μ.isCoupling_quantileCoupling ν
  let _ : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hfst : HasLaw Prod.fst μ π := hπ.measurePreserving_fst.hasLaw
  have hsnd : HasLaw Prod.snd ν π := hπ.measurePreserving_snd.hasLaw
  have hmapfst : HasLaw (fun z : ℝ × ℝ ↦ g z.1) (μ.map g) π :=
    (hasLaw_map hg.measurable.aemeasurable).fun_comp hfst
  have hmapsnd : HasLaw (fun z : ℝ × ℝ ↦ g z.2) (ν.map g) π :=
    (hasLaw_map hg.measurable.aemeasurable).fun_comp hsnd
  intro x
  refine hmapfst.cdf_le_of_ae_le hmapsnd ?_ x
  filter_upwards [μ.ae_fst_le_snd_quantileCoupling ν hμν] with z hz
  exact hg hz

/-- Convolving two pairs of comparably ordered real probability laws preserves the reversed cdf
comparison. -/
theorem cdf_conv_le_cdf_conv {μ₁ ν₁ μ₂ ν₂ : Measure ℝ} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]
    (h₁ : ∀ x, cdf ν₁ x ≤ cdf μ₁ x) (h₂ : ∀ x, cdf ν₂ x ≤ cdf μ₂ x) :
    ∀ x, cdf (ν₁ ∗ ν₂) x ≤ cdf (μ₁ ∗ μ₂) x := by
  let π₁ := μ₁.quantileCoupling ν₁
  let π₂ := μ₂.quantileCoupling ν₂
  have hπ₁ : TauCeti.IsCoupling π₁ μ₁ ν₁ := μ₁.isCoupling_quantileCoupling ν₁
  have hπ₂ : TauCeti.IsCoupling π₂ μ₂ ν₂ := μ₂.isCoupling_quantileCoupling ν₂
  let P := π₁.prod π₂
  let _ : IsProbabilityMeasure π₁ := hπ₁.isProbabilityMeasure
  let _ : IsProbabilityMeasure π₂ := hπ₂.isProbabilityMeasure
  let _ : IsProbabilityMeasure P := inferInstance
  have hμ₁ : HasLaw (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.1.1) μ₁ P :=
    hπ₁.measurePreserving_fst.hasLaw.fun_comp
      (measurePreserving_fst (μ := π₁) (ν := π₂)).hasLaw
  have hμ₂ : HasLaw (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.2.1) μ₂ P :=
    hπ₂.measurePreserving_fst.hasLaw.fun_comp
      (measurePreserving_snd (μ := π₁) (ν := π₂)).hasLaw
  have hν₁ : HasLaw (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.1.2) ν₁ P :=
    hπ₁.measurePreserving_snd.hasLaw.fun_comp
      (measurePreserving_fst (μ := π₁) (ν := π₂)).hasLaw
  have hν₂ : HasLaw (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.2.2) ν₂ P :=
    hπ₂.measurePreserving_snd.hasLaw.fun_comp
      (measurePreserving_snd (μ := π₁) (ν := π₂)).hasLaw
  have hindepμ :
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.1.1) ⟂ᵢ[P]
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.2.1) :=
    indepFun_prod measurable_fst measurable_fst
  have hindepν :
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.1.2) ⟂ᵢ[P]
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.2.2) :=
    indepFun_prod measurable_snd measurable_snd
  have hsumμ : HasLaw (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.1.1 + z.2.1)
      (μ₁ ∗ μ₂) P := hindepμ.hasLaw_fun_add hμ₁ hμ₂
  have hsumν : HasLaw (fun z : (ℝ × ℝ) × (ℝ × ℝ) ↦ z.1.2 + z.2.2)
      (ν₁ ∗ ν₂) P := hindepν.hasLaw_fun_add hν₁ hν₂
  have hle : ∀ᵐ z ∂P, z.1.1 + z.2.1 ≤ z.1.2 + z.2.2 := by
    rw [ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) (by fun_prop))]
    filter_upwards [μ₁.ae_fst_le_snd_quantileCoupling ν₁ h₁] with z₁ hz₁
    filter_upwards [μ₂.ae_fst_le_snd_quantileCoupling ν₂ h₂] with z₂ hz₂
    exact add_le_add hz₁ hz₂
  exact fun x ↦ hsumμ.cdf_le_of_ae_le hsumν hle x

end MeasureTheory.Measure
