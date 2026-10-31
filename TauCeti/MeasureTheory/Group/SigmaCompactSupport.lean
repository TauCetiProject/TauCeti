/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.StronglyMeasurable.SigmaCompact
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.SigmaCompact

/-!
# Integrable functions on a locally compact group live on a σ-compact open subgroup

A Haar measure on a locally compact group that is not σ-compact is not σ-finite, so Fubini's
theorem does not apply to it directly. If it is regular, as `MeasureTheory.Measure.haar` is, then
it is inner regular for compact sets on sets of finite measure, and countably many integrable
functions for it vanish almost everywhere outside a σ-compact set
(`MeasureTheory.exists_isSigmaCompact_forall_ae_eq_zero`). That set lies in a σ-compact open
subgroup (`IsSigmaCompact.exists_openSubgroup`). The restriction of the measure to this subgroup
is σ-finite (`IsSigmaCompact.sigmaFinite_restrict`), and since the subgroup is open it contains a
neighbourhood of the identity, so convolution kernels supported near the identity can be chosen
inside it as well.

## Main results

* `MeasureTheory.exists_openSubgroup_isSigmaCompact_forall_ae_eq_zero`: countably many almost
  everywhere finitely strongly measurable functions, for instance integrable functions, vanish
  almost everywhere outside a single σ-compact open subgroup.
-/

public section

open Set

namespace MeasureTheory

variable {G β ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G]
  {μ : Measure G} [μ.InnerRegularCompactLTTop] [Zero β] [TopologicalSpace β] [T2Space β]
  [Countable ι]

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
  obtain ⟨t, ht, hft⟩ := exists_isSigmaCompact_forall_ae_eq_zero hf
  obtain ⟨H, htH, hH⟩ := ht.exists_openSubgroup
  exact ⟨H, hH, fun i ↦ ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 htH) (hft i)⟩

end MeasureTheory
