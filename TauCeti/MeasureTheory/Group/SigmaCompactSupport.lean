/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.SigmaCompact
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.SigmaCompact
import TauCeti.Topology.Compactness.Compact

/-!
# σ-compact open subgroups containing sets of σ-finite restriction and integrable functions

A Haar measure on a locally compact group that is not σ-compact is not σ-finite, so Fubini's
theorem does not apply to it directly. If `μ` is inner regular for compact sets on sets of finite
measure and positive on nonempty open sets, every open set `V` of finite measure lies in a single
σ-compact open subgroup `H`: inner compact approximations to `V` generate `H`, leaving the open
difference `V \ H` of measure zero and hence empty, without requiring `T2Space G`. When `μ` is also
outer regular, outer open approximations extend this to any set `s` on which `μ` has σ-finite
restriction (`[SigmaFinite (μ.restrict s)]`), in particular to any finite-measure or null set.

On a locally compact Hausdorff group, countably many almost everywhere finitely strongly measurable
functions vanish almost everywhere outside a σ-compact set
(`MeasureTheory.exists_isSigmaCompact_forall_ae_eq_zero`). Adjoining any prescribed σ-compact set—in
particular a compact neighbourhood of the identity—still leaves a σ-compact set, which lies in a
σ-compact open subgroup (`IsSigmaCompact.exists_openSubgroup`). The restriction of the measure to
this subgroup is σ-finite (`IsSigmaCompact.sigmaFinite_restrict`), and since the subgroup is open it
contains a neighbourhood of the identity, so convolution kernels supported near the identity can be
chosen inside it as well.

## Main results

* `IsOpen.exists_openSubgroup_isSigmaCompact_of_measure_lt_top`: on a locally compact group
  with `[μ.IsOpenPosMeasure]` and `[μ.InnerRegularCompactLTTop]`, every open set of finite measure
  is contained in a σ-compact open subgroup (no `T2Space G` assumption is required).
* `MeasureTheory.exists_openSubgroup_isSigmaCompact_of_sigmaFinite_restrict`: if `μ` is also outer
  regular, every set `s` with `[SigmaFinite (μ.restrict s)]` is contained in a single σ-compact open
  subgroup (no `T2Space G` assumption is required).
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
open scoped ENNReal Topology

namespace MeasureTheory

section SigmaCompactSet

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

/-- **Open sets of finite measure lie in a σ-compact open subgroup.** On a locally compact group
with a measure `μ` that is positive on nonempty open sets and inner regular for compact sets on sets
of finite measure, every open set `V` with `μ V < ∞` is contained in a σ-compact open subgroup. -/
@[to_additive /-- **Open sets of finite measure lie in a σ-compact open additive subgroup.** On a
locally compact additive group with a measure `μ` that is positive on nonempty open sets and inner
regular for compact sets on sets of finite measure, every open set `V` with `μ V < ∞` is contained
in a σ-compact open additive subgroup. -/]
theorem _root_.IsOpen.exists_openSubgroup_isSigmaCompact_of_measure_lt_top {μ : Measure G}
    [μ.IsOpenPosMeasure] [μ.InnerRegularCompactLTTop] {V : Set G} (hVo : IsOpen V)
    (hVμ : μ V < ∞) :
    ∃ H : OpenSubgroup G, V ⊆ H ∧ IsSigmaCompact (H : Set G) := by
  have hK (n : ℕ) : ∃ K, K ⊆ V ∧ IsCompact K ∧ μ V < μ K + (n : ℝ≥0∞)⁻¹ :=
    hVo.measurableSet.exists_isCompact_lt_add hVμ.ne
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  choose K hKV hKc hKμ using hK
  obtain ⟨H, hKH, hH⟩ := (isSigmaCompact_iUnion_of_isCompact K hKc).exists_openSubgroup
  have hVH_null : μ (V \ (H : Set G)) = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
    have hVH_lt : μ (V \ (V ∩ (H : Set G))) < (n : ℝ≥0∞)⁻¹ :=
      measure_sdiff_lt_of_lt_add (hVo.inter H.isOpen).measurableSet.nullMeasurableSet
        inter_subset_left ((measure_mono inter_subset_left).trans_lt hVμ).ne <|
          (hKμ n).trans_le <| add_le_add_left
            (measure_mono (subset_inter (hKV n) ((subset_iUnion K n).trans hKH))) _
    rw [sdiff_self_inter] at hVH_lt
    exact hn.not_ge hVH_lt.le
  exact ⟨H, sdiff_eq_empty.1 (((hVo.sdiff H.isClosed).measure_eq_zero_iff μ).1 hVH_null), hH⟩

/-- **Sets of σ-finite restriction lie in a σ-compact open subgroup.** On a locally compact group
with an outer regular measure `μ` that is positive on nonempty open sets and inner regular for
compact sets on sets of finite measure, every subset `s` of `G` with `[SigmaFinite (μ.restrict s)]`
is contained in a single σ-compact open subgroup. -/
@[to_additive /-- **Sets of σ-finite restriction lie in a σ-compact open additive subgroup.** On a
locally compact additive group with an outer regular measure `μ` that is positive on nonempty open
sets and inner regular for compact sets on sets of finite measure, every subset `s` of `G` with
`[SigmaFinite (μ.restrict s)]` is contained in a single σ-compact open additive subgroup. -/]
theorem exists_openSubgroup_isSigmaCompact_of_sigmaFinite_restrict (μ : Measure G)
    [μ.IsOpenPosMeasure] [μ.InnerRegularCompactLTTop] [μ.OuterRegular] (s : Set G)
    [SigmaFinite (μ.restrict s)] :
    ∃ H : OpenSubgroup G, s ⊆ H ∧ IsSigmaCompact (H : Set G) := by
  let E : ℕ → Set G := spanningSets (μ.restrict s)
  have hEs_lt (n : ℕ) : μ (E n ∩ s) < ∞ := by
    rw [← Measure.restrict_apply (measurableSet_spanningSets (μ.restrict s) n)]
    exact measure_spanningSets_lt_top (μ.restrict s) n
  have hopen (n : ℕ) : ∃ V ⊇ E n ∩ s, IsOpen V ∧ μ V < μ (E n ∩ s) + 1 :=
    (E n ∩ s).exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right (hEs_lt n).ne one_ne_zero)
  choose V hEV hVo hVμ using hopen
  choose H hVH hHsc using fun n => (hVo n).exists_openSubgroup_isSigmaCompact_of_measure_lt_top
    ((hVμ n).trans (ENNReal.add_lt_top.2 ⟨hEs_lt n, ENNReal.one_lt_top⟩))
  obtain ⟨U, hHU, hUsc⟩ := OpenSubgroup.exists_isSigmaCompact_le hHsc
  refine ⟨U, fun x hx => ?_, hUsc⟩
  obtain ⟨n, hn⟩ := mem_iUnion.1 ((iUnion_spanningSets (μ.restrict s)).symm ▸ mem_univ x)
  exact hHU n (hVH n (hEV n ⟨hn, hx⟩))

end SigmaCompactSet

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
