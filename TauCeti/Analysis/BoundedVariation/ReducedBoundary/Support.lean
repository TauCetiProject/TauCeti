/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Analysis.BoundedVariation.DeGiorgi

/-!
# Points of the reduced boundary lie in the support of `Hⁿ⁻¹ ⌊ ∂*s`

Let `Ω` be an open set of a finite-dimensional real inner product space `E` of dimension `n ≥ 2`
and `s` a set. Every point `x` of the reduced boundary `∂*s` lies in the support of the measure
`Hⁿ⁻¹ ⌊ ∂*s` (`TauCeti.reducedBoundary_subset_support_restrict`): `x` lies in the support of
the perimeter measure `|Dχ_s|` (`TauCeti.variationMeasure_preimage_closedBall_ne_zero`), which is
`Hⁿ⁻¹ ⌊ ∂*s` by De Giorgi's theorem (`TauCeti.variationMeasure_eq_comap_restrict_reducedBoundary`).

Consequently `∂*s` lies in the closure of any set `T` containing `Hⁿ⁻¹`-almost every point of
`∂*s` (`TauCeti.reducedBoundary_subset_closure_inter_of_ae`), so the closure of `∂*s` is the
closure of `∂*s ∩ T` (`TauCeti.closure_reducedBoundary_eq_closure_inter_of_ae`): the closure of
the reduced boundary does not see `Hⁿ⁻¹`-null subsets of it.
-/

public section

open MeasureTheory TopologicalSpace Set Metric Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s T : Set E}

/-- **The reduced boundary lies in the support of its Hausdorff measure.** In dimension `n ≥ 2`,
every point of `∂*s` lies in the support of `Hⁿ⁻¹ ⌊ ∂*s`. -/
theorem reducedBoundary_subset_support_restrict (hn : 2 ≤ finrank ℝ E) :
    reducedBoundary volume Ω s ⊆
      (μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s)).support := by
  intro x hx
  rw [Metric.nhds_basis_closedBall.mem_measureSupport]
  intro r hr
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet
  have h := variationMeasure_preimage_closedBall_ne_zero hx hr
  rw [variationMeasure_eq_comap_restrict_reducedBoundary hn,
    hemb.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe,
    Measure.restrict_apply (measurableSet_closedBall.inter Ω.isOpen.measurableSet)] at h
  rw [Measure.restrict_apply measurableSet_closedBall, pos_iff_ne_zero]
  exact fun h0 => h (measure_mono_null (inter_subset_inter_left _ inter_subset_left) h0)

/-- In dimension `n ≥ 2`, the reduced boundary `∂*s` lies in the closure of `∂*s ∩ T` for every
set `T` containing `Hⁿ⁻¹`-almost every point of `∂*s`. -/
theorem reducedBoundary_subset_closure_inter_of_ae (hn : 2 ≤ finrank ℝ E)
    (hT : ∀ᵐ y ∂μHE[finrank ℝ E - 1], y ∈ reducedBoundary volume Ω s → y ∈ T) :
    reducedBoundary volume Ω s ⊆ closure (reducedBoundary volume Ω s ∩ T) := by
  intro x hx
  have hx' := reducedBoundary_subset_support_restrict hn hx
  have hae : reducedBoundary volume Ω s =ᵐ[μHE[finrank ℝ E - 1]]
      (reducedBoundary volume Ω s ∩ T : Set E) := by
    filter_upwards [hT] with y hy
    exact ⟨fun h => ⟨h, hy h⟩, fun h => h.1⟩
  rw [Measure.restrict_congr_set hae] at hx'
  exact (Measure.support_restrict_subset hx').1

/-- In dimension `n ≥ 2`, the closure of the reduced boundary `∂*s` is the closure of `∂*s ∩ T`
for every set `T` containing `Hⁿ⁻¹`-almost every point of `∂*s`. -/
theorem closure_reducedBoundary_eq_closure_inter_of_ae (hn : 2 ≤ finrank ℝ E)
    (hT : ∀ᵐ y ∂μHE[finrank ℝ E - 1], y ∈ reducedBoundary volume Ω s → y ∈ T) :
    closure (reducedBoundary volume Ω s) = closure (reducedBoundary volume Ω s ∩ T) :=
  (closure_minimal (reducedBoundary_subset_closure_inter_of_ae hn hT) isClosed_closure).antisymm
    (closure_mono inter_subset_left)

end TauCeti
