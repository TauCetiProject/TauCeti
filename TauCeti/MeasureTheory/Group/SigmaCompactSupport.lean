/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.StronglyMeasurable.SigmaCompact
public import TauCeti.MeasureTheory.Integral.PeakFunction
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.SigmaCompact
import TauCeti.Topology.Compactness.Compact

/-!
# Integrable functions and peak kernels on σ-compact open subgroups

A Haar measure on a locally compact group that is not σ-compact is not σ-finite, so Fubini's
theorem does not apply to it directly. If it is regular, as `MeasureTheory.Measure.haar` is, then
it is inner regular for compact sets on sets of finite measure, and countably many integrable
functions for it vanish almost everywhere outside a σ-compact set
(`MeasureTheory.exists_isSigmaCompact_forall_ae_eq_zero`). Adjoining any prescribed σ-compact set—in
particular a compact neighbourhood of the identity—still leaves a σ-compact set, which lies in a
σ-compact open subgroup (`IsSigmaCompact.exists_openSubgroup`). The restriction of the measure to
this subgroup is σ-finite (`IsSigmaCompact.sigmaFinite_restrict`,
`OpenSubgroup.sigmaFinite_comap`), and since the subgroup is open it contains a neighbourhood of the
identity, so continuous and `L¹` peak kernels supported inside any given identity neighbourhood can
be chosen inside the subgroup as well.

## Main results

* `MeasureTheory.exists_openSubgroup_subset_isSigmaCompact_forall_ae_eq_zero`: encloses any
  prescribed σ-compact set together with the supports of countably many `AEFinStronglyMeasurable`
  functions in a single σ-compact open subgroup.
* `MeasureTheory.exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero`: specialization with no
  prescribed subset.
* `MeasureTheory.exists_compact_mem_nhds_subset_openSubgroup_isSigmaCompact_forall_ae_eq_zero`:
  adjoins a compact neighbourhood of the identity to a σ-compact open subgroup supporting countably
  many `AEFinStronglyMeasurable` functions.
* `OpenSubgroup.exists_nonneg_tsupport_subset_integral_eq_one` and
  `OpenSubgroup.exists_integral_eq_one_norm_eq_one`: nonnegative `C_c(G, ℝ)` and norm-one
  `L¹(G, μ; 𝕜)` unit-integral kernels supported inside both a given identity neighbourhood `U` and
  an open subgroup `H`.
-/

public section

open Filter MeasureTheory Set
open scoped CompactlySupported Topology

namespace MeasureTheory

section SigmaCompactSupport

variable {G β ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] [Zero β] [TopologicalSpace β] [T2Space β]
  [Countable ι]

/-- **Countably many finitely strongly measurable functions and a σ-compact set live on a single
σ-compact open subgroup.** On a locally compact Hausdorff group with a measure that is inner regular
for compact sets on sets of finite measure, any σ-compact set `s` and the supports of countably many
almost everywhere finitely strongly measurable functions lie inside one σ-compact open subgroup. -/
@[to_additive /-- **Countably many finitely strongly measurable functions and a σ-compact set live
on a single σ-compact open additive subgroup.** On a locally compact Hausdorff additive group with a
measure that is inner regular for compact sets on sets of finite measure, any σ-compact set `s` and
the supports of countably many almost everywhere finitely strongly measurable functions lie inside
one σ-compact open subgroup. -/]
theorem exists_openSubgroup_subset_isSigmaCompact_forall_ae_eq_zero {s : Set G}
    (hs : IsSigmaCompact s) {f : ι → G → β} (hf : ∀ i, AEFinStronglyMeasurable (f i) μ) :
    ∃ H : OpenSubgroup G, s ⊆ H ∧ IsSigmaCompact (H : Set G) ∧
      ∀ i, f i =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  obtain ⟨t, ht, hft⟩ := exists_isSigmaCompact_forall_ae_eq_zero hf
  obtain ⟨H, hstH, hH⟩ := (hs.union ht).exists_openSubgroup
  exact ⟨H, subset_union_left.trans hstH, hH,
    fun i ↦ ae_restrict_of_ae_restrict_of_subset
      (compl_subset_compl.2 (subset_union_right.trans hstH)) (hft i)⟩

/-- **Countably many integrable functions live on a σ-compact open subgroup.** On a locally
compact group with a measure that is inner regular for compact sets on sets of finite measure,
such as a regular Haar measure, countably many almost everywhere finitely strongly measurable
functions vanish almost everywhere outside a single σ-compact open subgroup. -/
@[to_additive /-- **Countably many integrable functions live on a σ-compact open subgroup.** On a
locally compact additive group with a measure that is inner regular for compact sets on sets of
finite measure, such as a regular additive Haar measure, countably many almost everywhere finitely
strongly measurable functions vanish almost everywhere outside a single σ-compact open
subgroup. -/]
theorem exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero {f : ι → G → β}
    (hf : ∀ i, AEFinStronglyMeasurable (f i) μ) :
    ∃ H : OpenSubgroup G, IsSigmaCompact (H : Set G) ∧
      ∀ i, f i =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  obtain ⟨H, -, hH, hfH⟩ :=
    exists_openSubgroup_subset_isSigmaCompact_forall_ae_eq_zero isSigmaCompact_empty hf
  exact ⟨H, hH, hfH⟩

/-- **Adjoining a compact identity neighbourhood to a σ-compact open subgroup.** Given countably
many almost everywhere finitely strongly measurable functions on a locally compact Hausdorff group,
there exist a compact neighbourhood `K` of `1` and a σ-compact open subgroup `H` containing `K`
outside which all the functions vanish almost everywhere. -/
@[to_additive /-- **Adjoining a compact zero neighbourhood to a σ-compact open additive subgroup.**
Given countably many almost everywhere finitely strongly measurable functions on a locally compact
Hausdorff additive group, there exist a compact neighbourhood `K` of `0` and a σ-compact open
subgroup `H` containing `K` outside which all the functions vanish almost everywhere. -/]
theorem exists_compact_mem_nhds_subset_openSubgroup_isSigmaCompact_forall_ae_eq_zero
    {f : ι → G → β} (hf : ∀ i, AEFinStronglyMeasurable (f i) μ) :
    ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 (1 : G) ∧
      ∃ H : OpenSubgroup G, K ⊆ H ∧ IsSigmaCompact (H : Set G) ∧
        ∀ i, f i =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  exact ⟨K, hK, hK1,
    exists_openSubgroup_subset_isSigmaCompact_forall_ae_eq_zero hK.isSigmaCompact hf⟩

end SigmaCompactSupport

end MeasureTheory

namespace OpenSubgroup

section Kernels

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (H : OpenSubgroup G)

/-- **Continuous peak kernels inside an open subgroup.** On a locally compact `R₁` group with a
measure positive on nonempty open sets and finite on compact sets, every neighbourhood `U` of `1`
carries a nonnegative compactly supported continuous function `φ` of unit integral supported inside
both `U` and `H`. -/
@[to_additive exists_nonneg_tsupport_subset_integral_eq_one
/-- **Continuous peak kernels inside an open additive subgroup.** On a locally compact
`R₁` additive group with a measure positive on nonempty open sets and finite on compact sets, every
neighbourhood `U` of `0` carries a nonnegative compactly supported continuous function `φ` of unit
integral supported inside both `U` and `H`. -/]
theorem exists_nonneg_tsupport_subset_integral_eq_one [R1Space G] [LocallyCompactSpace G]
    (μ : Measure G) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ φ : C_c(G, ℝ), 0 ≤ φ ∧ tsupport φ ⊆ U ∧ tsupport φ ⊆ H ∧ ∫ x, φ x ∂μ = 1 := by
  obtain ⟨φ, hφ0, hφUH, hφ1⟩ := TauCeti.exists_nonneg_tsupport_subset_integral_eq_one μ
    (inter_mem hU (H.isOpen.mem_nhds H.one_mem))
  exact ⟨φ, hφ0, hφUH.trans inter_subset_left, hφUH.trans inter_subset_right, hφ1⟩

/-- **`L¹` peak kernels inside an open subgroup.** For a locally finite measure positive on nonempty
open sets, every neighbourhood `U` of `1` carries an `L¹` class `f` of unit integral and unit `L¹`
norm vanishing almost everywhere outside both `U` and `H`. -/
@[to_additive (dont_translate := 𝕜) exists_integral_eq_one_norm_eq_one
/-- **`L¹` peak kernels inside an open additive subgroup.** For a locally finite measure positive on
nonempty open sets, every neighbourhood `U` of `0` carries an `L¹` class `f` of unit integral and
unit `L¹` norm vanishing almost everywhere outside both `U` and `H`. -/]
theorem exists_integral_eq_one_norm_eq_one (𝕜 : Type*) [RCLike 𝕜] (μ : Measure G)
    [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ f : G →₁[μ] 𝕜, ∫ x, f x ∂μ = 1 ∧ ‖f‖ = 1 ∧
      (∀ᵐ x ∂μ, x ∉ U → f x = 0) ∧ (f : G → 𝕜) =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  obtain ⟨f, hf1, hfn, hfUH⟩ := TauCeti.exists_integral_eq_one_norm_eq_one 𝕜 μ
    (inter_mem hU (H.isOpen.mem_nhds H.one_mem))
  refine ⟨f, hf1, hfn, ?_, (ae_restrict_iff' H.isOpen.measurableSet.compl).2 ?_⟩
  · filter_upwards [hfUH] with x hx hxU
    exact hx fun hxUH ↦ hxU hxUH.1
  · filter_upwards [hfUH] with x hx hxH
    exact hx fun hxUH ↦ hxH hxUH.2

end Kernels

end OpenSubgroup
