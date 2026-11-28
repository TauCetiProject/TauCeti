/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Integrals on a topological group factored through an open subgroup

For a left-invariant Borel measure `μ` on a separable topological group `G` and an open subgroup
`J ≤ G`, the quotient `G ⧸ J` is countable and discrete, and the pushforward of `μ` along
`QuotientGroup.mk : G → G ⧸ J` is `μ J • Measure.count`. Consequently, the Bochner integral or
lower Lebesgue integral of any function factored through `G ⧸ J` equals the measure of `J` times
the sum over cosets.

## Main results

* `TauCeti.inv_mul_out_coe_mem`: `y⁻¹ * (y : G ⧸ J).out ∈ J`.
* `TauCeti.lintegral_comp_quotientMk`: for `f : G ⧸ J → ℝ≥0∞`,
  `∫⁻ y : G, f y ∂μ = μ J * ∑' q : G ⧸ J, f q`.
* `TauCeti.integral_comp_quotientMk`: for `f : G ⧸ J → E`,
  `∫ y : G, f y ∂μ = μ.real J • ∑' q : G ⧸ J, f q`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/New/Spanning/MainTerm/KloostermanSum.lean`
(`New.integral_comp_quotientMk`, `New.inv_mul_out_coe_mem`).
-/

@[expose] public section

namespace TauCeti

open MeasureTheory

/-- Every element `y` of a group `G` differs from its chosen coset representative
`(y : G ⧸ J).out` by an element of `J`. -/
theorem inv_mul_out_coe_mem {G : Type*} [Group G] (J : Subgroup G) (y : G) :
    y⁻¹ * (y : G ⧸ J).out ∈ J :=
  QuotientGroup.eq.mp (y : G ⧸ J).out_eq'.symm

/-- For a left-invariant Borel measure `μ` on a separable topological group `G` and an open
subgroup `J ≤ G`, the lower Lebesgue integral of a function on `G ⧸ J` equals `μ J` times its sum
over the cosets. -/
theorem lintegral_comp_quotientMk {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [TopologicalSpace.SeparableSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] {J : Subgroup G} (hJ : IsOpen (J : Set G)) (f : G ⧸ J → ENNReal) :
    ∫⁻ y : G, f y ∂μ = μ J * ∑' q : G ⧸ J, f q := by
  have : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJ
  have : TopologicalSpace.SeparableSpace (G ⧸ J) := by
    have h := ((TopologicalSpace.isSeparable_univ_iff (α := G)).mpr inferInstance).image
      (QuotientGroup.continuous_mk (N := J))
    rw [Set.image_univ, (QuotientGroup.mk_surjective (s := J)).range_eq] at h
    exact TopologicalSpace.isSeparable_univ_iff.mp h
  have : Countable (G ⧸ J) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : MeasurableSpace (G ⧸ J) := ⊤
  have h_meas : Measurable (QuotientGroup.mk : G → G ⧸ J) := fun s _ ↦
    ((isOpen_discrete s).preimage QuotientGroup.continuous_mk).measurableSet
  have h_map : μ.map QuotientGroup.mk = μ J • (Measure.count : Measure (G ⧸ J)) := by
    refine Measure.ext_of_singleton fun q ↦ ?_
    obtain ⟨a : G, rfl⟩ := QuotientGroup.mk_surjective q
    have h_coset : QuotientGroup.mk ⁻¹' {(a : G ⧸ J)} = (fun y : G ↦ a⁻¹ * y) ⁻¹' J :=
      Set.ext fun y ↦ by simp [eq_comm (b := (a : G ⧸ J)), QuotientGroup.eq]
    simp [Measure.map_apply h_meas (measurableSet_singleton _), h_coset]
  rw [← lintegral_map (measurable_from_top) h_meas, h_map, lintegral_smul_measure, lintegral_count,
    smul_eq_mul]

/-- For a left-invariant Borel measure `μ` on a separable topological group `G` and an open
subgroup `J ≤ G`, the Bochner integral of a function on `G ⧸ J` equals `μ.real J` times its sum
over the cosets (both sides vanish if the sum does not converge). -/
theorem integral_comp_quotientMk {G E : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [TopologicalSpace.SeparableSpace G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (μ : Measure G)
    [μ.IsMulLeftInvariant] {J : Subgroup G} (hJ : IsOpen (J : Set G)) (f : G ⧸ J → E) :
    ∫ y : G, f y ∂μ = μ.real J • ∑' q : G ⧸ J, f q := by
  have : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJ
  have : TopologicalSpace.SeparableSpace (G ⧸ J) := by
    have h := ((TopologicalSpace.isSeparable_univ_iff (α := G)).mpr inferInstance).image
      (QuotientGroup.continuous_mk (N := J))
    rw [Set.image_univ, (QuotientGroup.mk_surjective (s := J)).range_eq] at h
    exact TopologicalSpace.isSeparable_univ_iff.mp h
  have : Countable (G ⧸ J) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let : MeasurableSpace (G ⧸ J) := ⊤
  have h_meas : Measurable (QuotientGroup.mk : G → G ⧸ J) := fun s _ ↦
    ((isOpen_discrete s).preimage QuotientGroup.continuous_mk).measurableSet
  have h_map : μ.map QuotientGroup.mk = μ J • (Measure.count : Measure (G ⧸ J)) := by
    refine Measure.ext_of_singleton fun q ↦ ?_
    obtain ⟨a : G, rfl⟩ := QuotientGroup.mk_surjective q
    have h_coset : QuotientGroup.mk ⁻¹' {(a : G ⧸ J)} = (fun y : G ↦ a⁻¹ * y) ⁻¹' J :=
      Set.ext fun y ↦ by simp [eq_comm (b := (a : G ⧸ J)), QuotientGroup.eq]
    simp [Measure.map_apply h_meas (measurableSet_singleton _), h_coset]
  have h_count : ∫ q : G ⧸ J, f q ∂Measure.count = ∑' q : G ⧸ J, f q := by
    by_cases hf : Integrable f Measure.count
    · simp [integral_countable hf]
    · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
      rwa [← summable_norm_iff, ← integrable_count_iff]
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  rw [← integral_map h_meas.aemeasurable measurable_from_top.aestronglyMeasurable, h_map,
    integral_smul_measure, h_count, Measure.real]

end TauCeti
