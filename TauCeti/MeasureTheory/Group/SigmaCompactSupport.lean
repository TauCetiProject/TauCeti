/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.StronglyMeasurable.SigmaCompact
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.SigmaCompact
import TauCeti.Topology.Compactness.Compact

/-!
# Integrable functions on a locally compact group live on a σ-compact open subgroup

A Haar measure on a locally compact group that is not σ-compact is not σ-finite, so Fubini's
theorem does not apply to it directly. If it is regular, as `MeasureTheory.Measure.haar` is, then
it is inner regular for compact sets on sets of finite measure, and countably many integrable
functions for it vanish almost everywhere outside a σ-compact set
(`MeasureTheory.exists_isSigmaCompact_forall_ae_eq_zero`). Adjoining any prescribed σ-compact set—in
particular a compact neighbourhood of the identity—still leaves a σ-compact set, which lies in a
σ-compact open subgroup (`IsSigmaCompact.exists_openSubgroup`). The restriction of the measure to
this subgroup is σ-finite (`IsSigmaCompact.sigmaFinite_restrict`), and since the subgroup is open it
contains a neighbourhood of the identity, so convolution kernels supported near the identity can be
chosen inside it as well.

## Main results

* `MeasureTheory.exists_openSubgroup_subset_isSigmaCompact_forall_ae_eq_zero`: for any prescribed
  σ-compact set `s` and countably many `AEFinStronglyMeasurable` functions, there exists a
  σ-compact open subgroup `H` containing `s` outside which every function vanishes `μ`-almost
  everywhere.
* `MeasureTheory.exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero`: specialization with no
  prescribed subset.
* `MeasureTheory.exists_compact_mem_nhds_subset_openSubgroup_isSigmaCompact_forall_ae_eq_zero`:
  produces a compact neighbourhood of the identity and a σ-compact open subgroup `H` containing it
  outside which countably many `AEFinStronglyMeasurable` functions vanish `μ`-almost everywhere.
-/

public section

open Set
open scoped Topology

namespace MeasureTheory

section SigmaCompactSupport

variable {G β ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] [Zero β] [TopologicalSpace β] [T2Space β]
  [Countable ι]

/-- **Countably many finitely strongly measurable functions and a σ-compact set live on a single
σ-compact open subgroup.** On a locally compact Hausdorff group with a measure that is inner regular
for compact sets on sets of finite measure, for any σ-compact set `s` and countably many almost
everywhere finitely strongly measurable functions, there exists a σ-compact open subgroup `H`
containing `s` outside which every function vanishes `μ`-almost everywhere. -/
@[to_additive /-- **Countably many finitely strongly measurable functions and a σ-compact set live
on a single σ-compact open additive subgroup.** On a locally compact Hausdorff additive group with a
measure that is inner regular for compact sets on sets of finite measure, for any σ-compact set `s`
and countably many almost everywhere finitely strongly measurable functions, there exists a
σ-compact open subgroup `H` containing `s` outside which every function vanishes `μ`-almost
everywhere. -/]
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
