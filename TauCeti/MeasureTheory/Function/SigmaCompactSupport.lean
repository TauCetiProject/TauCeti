/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import TauCeti.MeasureTheory.Measure.Regular
public import TauCeti.Topology.Algebra.Group.SigmaCompact

/-!
# Integrable functions vanish outside a σ-compact set

Let `μ` be a measure on a Hausdorff space that is inner regular for compact sets on sets of finite
measure, such as a regular measure, and in particular any regular Haar measure on a locally
compact group. The measure need not be σ-finite. Nevertheless every integrable function, and
more generally every almost everywhere finitely strongly measurable function, vanishes almost
everywhere outside a σ-compact set
(`MeasureTheory.AEFinStronglyMeasurable.exists_isSigmaCompact_ae_eq_zero`). Indeed such a
function vanishes outside a set `t` on which `μ` is σ-finite, and inner regularity exhausts `t`,
up to a null set, by countably many compact sets.

On a σ-compact set a measure finite on compact sets is σ-finite
(`IsSigmaCompact.sigmaFinite_restrict`). In a locally compact group, countably many such
σ-compact sets lie in one σ-compact open subgroup. Thus countably many integrable functions on a
locally compact group all vanish almost everywhere outside a single σ-compact open subgroup `H`
(`MeasureTheory.exists_isSigmaCompact_openSubgroup_forall_ae_eq_zero`), and their integrals are
integrals over `H`, for a measure whose restriction to `H` is σ-finite. This lets Fubini-type
arguments for integrable functions on a group that is not σ-compact be carried out inside `H`.

## Main results

* `IsSigmaCompact.measurableSet`: σ-compact sets in a Hausdorff space are measurable.
* `IsSigmaCompact.sigmaFinite_restrict`: the restriction of a measure finite on compact sets to
  a σ-compact set is σ-finite.
* `MeasureTheory.AEFinStronglyMeasurable.exists_isSigmaCompact_ae_eq_zero`,
  `MeasureTheory.Integrable.exists_isSigmaCompact_ae_eq_zero`: such a function vanishes almost
  everywhere outside a σ-compact set.
* `MeasureTheory.exists_isSigmaCompact_forall_ae_eq_zero`: the same for countably many functions
  and one σ-compact set.
* `MeasureTheory.exists_isSigmaCompact_openSubgroup_forall_ae_eq_zero`: in a locally compact
  group, countably many such functions vanish almost everywhere outside one σ-compact open
  subgroup.

## References

* E. Hewitt, K. A. Ross, *Abstract Harmonic Analysis I*, Springer (1963), Theorem 5.7.
-/

public section

open Set Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]

section SigmaCompact

variable [OpensMeasurableSpace α] [T2Space α] {s : Set α}

/-- A σ-compact set in a Hausdorff space is measurable. -/
theorem IsSigmaCompact.measurableSet (hs : IsSigmaCompact s) : MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact .iUnion fun n ↦ (hK n).measurableSet

/-- The restriction of a measure that is finite on compact sets to a σ-compact set is
σ-finite. -/
theorem IsSigmaCompact.sigmaFinite_restrict (hs : IsSigmaCompact s) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] : MeasureTheory.SigmaFinite (μ.restrict s) := by
  have hsm := hs.measurableSet
  obtain ⟨K, hK, hKs⟩ := hs
  -- `α` is covered by the compact sets `K n` together with the null set `sᶜ`.
  refine MeasureTheory.Measure.sigmaFinite_of_countable (S := insert sᶜ (range K))
    ((countable_range K).insert _) ?_ ?_
  · rintro _ (rfl | ⟨n, rfl⟩)
    · simp [MeasureTheory.Measure.restrict_apply' hsm]
    · exact (MeasureTheory.Measure.restrict_apply_le _ _).trans_lt (hK n).measure_lt_top
  · rw [sUnion_insert, sUnion_range, hKs, compl_union_self]

end SigmaCompact

namespace MeasureTheory

variable [OpensMeasurableSpace α] [T2Space α] {μ : Measure α} [μ.InnerRegularCompactLTTop]
  {β : Type*} [TopologicalSpace β] [Zero β] [T2Space β]

/-- **Finitely strongly measurable functions vanish outside a σ-compact set.** For a measure that
is inner regular for compact sets on sets of finite measure, an almost everywhere finitely
strongly measurable function vanishes almost everywhere outside some σ-compact set. The measure
need not be σ-finite. -/
theorem AEFinStronglyMeasurable.exists_isSigmaCompact_ae_eq_zero {f : α → β}
    (hf : AEFinStronglyMeasurable f μ) : ∃ s, IsSigmaCompact s ∧ f =ᵐ[μ.restrict sᶜ] 0 := by
  obtain ⟨t, ht, hft, htμ⟩ := hf.exists_set_sigmaFinite
  -- Exhaust `t` by a σ-compact set up to a `μ`-null set.
  obtain ⟨s, -, hs, hst⟩ :=
    (nullMeasurableSet_univ (μ := μ.restrict t)).exists_isSigmaCompact_subset_ae_eq
  have hst : μ (sᶜ ∩ t) = 0 := by
    rwa [ae_eq_univ, Measure.restrict_apply hs.measurableSet.compl] at hst
  refine ⟨s, hs, ?_⟩
  rw [EventuallyEq, ae_restrict_iff' ht.compl] at hft
  rw [EventuallyEq, ae_restrict_iff' hs.measurableSet.compl]
  filter_upwards [hft, measure_eq_zero_iff_ae_notMem.1 hst] with x hxt hxst hxs
  exact hxt fun hx ↦ hxst ⟨hxs, hx⟩

/-- **Integrable functions vanish outside a σ-compact set.** For a measure that is inner regular
for compact sets on sets of finite measure, an integrable function vanishes almost everywhere
outside some σ-compact set. The measure need not be σ-finite. -/
theorem Integrable.exists_isSigmaCompact_ae_eq_zero {E : Type*} [NormedAddCommGroup E]
    {f : α → E} (hf : Integrable f μ) : ∃ s, IsSigmaCompact s ∧ f =ᵐ[μ.restrict sᶜ] 0 :=
  hf.aefinStronglyMeasurable.exists_isSigmaCompact_ae_eq_zero

/-- For a measure that is inner regular for compact sets on sets of finite measure, countably many
almost everywhere finitely strongly measurable functions all vanish almost everywhere outside one
σ-compact set. -/
theorem exists_isSigmaCompact_forall_ae_eq_zero {ι : Type*} [Countable ι] {f : ι → α → β}
    (hf : ∀ i, AEFinStronglyMeasurable (f i) μ) :
    ∃ s, IsSigmaCompact s ∧ ∀ i, f i =ᵐ[μ.restrict sᶜ] 0 := by
  choose s hs hfs using fun i ↦ (hf i).exists_isSigmaCompact_ae_eq_zero
  refine ⟨⋃ i, s i, isSigmaCompact_iUnion s hs, fun i ↦ ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 (subset_iUnion s i)) (hfs i)

/-- In a weakly locally compact group with a measure that is inner regular for compact sets on
sets of finite measure, such as a regular Haar measure, countably many almost everywhere finitely
strongly measurable functions (for example integrable functions) all vanish almost everywhere
outside one σ-compact open subgroup. -/
@[to_additive /-- In a weakly locally compact additive group with a measure that is inner regular
for compact sets on sets of finite measure, such as a regular additive Haar measure, countably many
almost everywhere finitely strongly measurable functions (for example integrable functions) all
vanish almost everywhere outside one σ-compact open additive subgroup. -/]
theorem exists_isSigmaCompact_openSubgroup_forall_ae_eq_zero {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {μ : Measure G} [μ.InnerRegularCompactLTTop]
    {ι : Type*} [Countable ι] {f : ι → G → β} (hf : ∀ i, AEFinStronglyMeasurable (f i) μ) :
    ∃ H : OpenSubgroup G, IsSigmaCompact (H : Set G) ∧
      ∀ i, f i =ᵐ[μ.restrict (H : Set G)ᶜ] 0 := by
  obtain ⟨s, hs, hfs⟩ := exists_isSigmaCompact_forall_ae_eq_zero hf
  obtain ⟨H, hsH, hH⟩ := hs.exists_isSigmaCompact_openSubgroup_superset
  exact ⟨H, hH, fun i ↦ ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 hsH) (hfs i)⟩

end MeasureTheory
