/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DeGiorgi

/-!
# The reduced boundary is the support of its Hausdorff measure

Let `Ω` be an open set of a finite-dimensional real inner product space `E` of dimension `n ≥ 2`
and `s` a set. Every closed ball of positive radius around a point `x` of the reduced boundary
`∂*s` meets `∂*s` in a set of positive `Hⁿ⁻¹` measure
(`TauCeti.euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_ne_zero`): the point `x` lies
in the support of the perimeter measure `|Dχ_s|`
(`TauCeti.variationMeasure_preimage_closedBall_ne_zero`), which is `Hⁿ⁻¹ ⌊ ∂*s` by De Giorgi's
theorem (`TauCeti.variationMeasure_eq_comap_restrict_reducedBoundary`).

Consequently `∂*s` lies in the closure of any set `T` containing `Hⁿ⁻¹`-almost every point of
`∂*s` (`TauCeti.reducedBoundary_subset_closure_inter_of_ae`), so the closure of `∂*s` is the
closure of `∂*s ∩ T` (`TauCeti.closure_reducedBoundary_eq_closure_inter_of_ae`): the closure of
the reduced boundary does not see `Hⁿ⁻¹`-null subsets of it.
-/

public section

open MeasureTheory TopologicalSpace Set Metric Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {s T : Set E} {x : E}

/-- **The reduced boundary has positive Hausdorff measure near each of its points.** In dimension
`n ≥ 2`, for `x ∈ ∂*s` and `r > 0`, `Hⁿ⁻¹(∂*s ∩ closedBall x r) ≠ 0`. -/
theorem euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_ne_zero
    (hn : 2 ≤ finrank ℝ E) (hx : x ∈ reducedBoundary volume Ω s) {r : ℝ} (hr : 0 < r) :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ closedBall x r) ≠ 0 := by
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    MeasurableEmbedding.subtypeVal Ω.isOpen.measurableSet
  have h := variationMeasure_preimage_closedBall_ne_zero hx hr
  rw [variationMeasure_eq_comap_restrict_reducedBoundary hn,
    hemb.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe,
    Measure.restrict_apply (measurableSet_closedBall.inter Ω.isOpen.measurableSet)] at h
  exact fun h0 => h (measure_mono_null (by intro y hy; exact ⟨hy.2, hy.1.1⟩) h0)

/-- In dimension `n ≥ 2`, the reduced boundary `∂*s` lies in the closure of `∂*s ∩ T` for every
set `T` containing `Hⁿ⁻¹`-almost every point of `∂*s`. -/
theorem reducedBoundary_subset_closure_inter_of_ae (hn : 2 ≤ finrank ℝ E)
    (hT : ∀ᵐ y ∂μHE[finrank ℝ E - 1], y ∈ reducedBoundary volume Ω s → y ∈ T) :
    reducedBoundary volume Ω s ⊆ closure (reducedBoundary volume Ω s ∩ T) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra! h
  refine euclideanHausdorffMeasure_reducedBoundary_inter_closedBall_ne_zero hn hx
    (half_pos hε) (measure_mono_null ?_ (ae_iff.1 hT))
  intro y hy hyT
  have h₁ := h y ⟨hy.1, hyT hy.1⟩
  have h₂ : dist y x ≤ ε / 2 := hy.2
  rw [dist_comm] at h₂
  linarith

/-- In dimension `n ≥ 2`, the closure of the reduced boundary `∂*s` is the closure of `∂*s ∩ T`
for every set `T` containing `Hⁿ⁻¹`-almost every point of `∂*s`. -/
theorem closure_reducedBoundary_eq_closure_inter_of_ae (hn : 2 ≤ finrank ℝ E)
    (hT : ∀ᵐ y ∂μHE[finrank ℝ E - 1], y ∈ reducedBoundary volume Ω s → y ∈ T) :
    closure (reducedBoundary volume Ω s) = closure (reducedBoundary volume Ω s ∩ T) :=
  (closure_minimal (reducedBoundary_subset_closure_inter_of_ae hn hT) isClosed_closure).antisymm
    (closure_mono inter_subset_left)

end TauCeti
