/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Hausdorff measure on the reduced boundary is at most the perimeter measure

Let `Ω` be an open set of a finite-dimensional real inner product space `E` of dimension
`n ≥ 2`, with Lebesgue measure, and let `s ⊆ E`. At every point of the reduced boundary `∂*s` of
`s` in `Ω`, the perimeter measure `|Dχ_s|` has density one with respect to the normalized
Hausdorff measure `μHE[n - 1]`
(`TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`). The density comparison for
Hausdorff measure (`MeasureTheory.Measure.mul_euclideanHausdorffMeasure_le_measure`) turns this
lower density bound into the measure inequality

`μHE[n - 1] (A) ≤ |Dχ_s| (A)`     for every `A ⊆ ∂*s`

(`TauCeti.euclideanHausdorffMeasure_le_variationMeasure_preimage`), with the sharp constant one
and with no measurability of `A`. In measure form, `μHE[n - 1]⌊∂*s ≤ |Dχ_s|`
(`TauCeti.euclideanHausdorffMeasure_restrict_reducedBoundary_le_map_variationMeasure`). This is one
of the two inequalities of the identity `|Dχ_s| = μHE[n - 1]⌊∂*s` in De Giorgi's structure theorem.
The reverse inequality uses the rectifiability of the reduced boundary and is not proved here.

Consequences:

* `TauCeti.euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter` and
  `TauCeti.euclideanHausdorffMeasure_reducedBoundary_le_perimeter`: the `(n - 1)`-dimensional
  measure of the reduced boundary is at most the perimeter, `μHE[n - 1] (∂*s ∩ U) ≤ P(s; U)` for
  every open `U ⊆ Ω`; in particular `μHE[n - 1] (∂*s) ≤ P(s; Ω)`.
* `TauCeti.euclideanHausdorffMeasure_reducedBoundary_inter_lt_top`: the reduced boundary has
  locally finite `μHE[n - 1]` measure in `Ω`, `μHE[n - 1] (∂*s ∩ K) < ∞` for every compact
  `K ⊆ Ω`, which is the finiteness hypothesis of the density theorem for countably rectifiable
  sets, for the pieces `∂*s ∩ K`.

The comparison in the other direction, `|Dχ_s| (A) ≤ n ω_n μH[n - 1] (A)` for `A ⊆ ∂*s` with the
raw Hausdorff measure and a nonsharp constant, is
`TauCeti.variationMeasure_preimage_le_mul_hausdorffMeasure`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 15.9
  (De Giorgi's structure theorem) and its proof.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.8 (the structure theorem for `∂*E`), using the density comparison of §2.4.2.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω U : Opens E} {s : Set E}

/-- **Hausdorff measure on the reduced boundary is at most the perimeter measure.** Let `E` have
dimension `n ≥ 2`, with Lebesgue measure. Every set `A` of points of the reduced boundary `∂*s` of
`s` in `Ω` satisfies `μHE[n - 1] (A) ≤ |Dχ_s| (A)`. No measurability of `A` is assumed. -/
theorem euclideanHausdorffMeasure_le_variationMeasure_preimage (hn : 2 ≤ finrank ℝ E) {A : Set E}
    (hA : A ⊆ reducedBoundary volume Ω s) :
    μHE[finrank ℝ E - 1] A ≤
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) := by
  have hAΩ : A ⊆ range ((↑) : Ω → E) := fun x hx => ⟨⟨x, reducedBoundary_subset (hA hx)⟩, rfl⟩
  -- The inclusion of `Ω` carries the subspace distance, as in `isometry_subtype_coe`.
  have hΩ : Isometry ((↑) : Ω → E) := fun _ _ => rfl
  rw [← image_preimage_eq_of_subset hAΩ, hΩ.euclideanHausdorffMeasure_image,
    preimage_image_eq _ Subtype.val_injective]
  refine ENNReal.le_of_forall_lt_one_mul_le fun t ht => ?_
  refine Measure.mul_euclideanHausdorffMeasure_le_measure _ _ fun y hy => ?_
  -- The density of `|Dχ_s|` at `y` is one, so it eventually exceeds `t < 1`.
  have hdens := tendsto_variationMeasure_closedBall_div_volume_closedBall hn (hA hy)
  refine ((hdens.eventually (lt_mem_nhds ht)).mono fun r hr => ?_).frequently
  rw [← Subtype.preimage_closedBall]
  exact ENNReal.mul_le_of_le_div hr.le

/-- **Hausdorff measure on the reduced boundary is at most the perimeter measure**, measure form.
Let `E` have dimension `n ≥ 2`, with Lebesgue measure. The restriction of `μHE[n - 1]` to the
reduced boundary of `s` in `Ω` is at most the perimeter measure `|Dχ_s|`, viewed as a measure on
the ambient space. -/
theorem euclideanHausdorffMeasure_restrict_reducedBoundary_le_map_variationMeasure
    (hn : 2 ≤ finrank ℝ E) :
    μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s) ≤
      (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) := by
  refine Measure.le_iff.2 fun N hN => ?_
  rw [Measure.restrict_apply hN, Measure.map_apply measurable_subtype_coe hN]
  exact (euclideanHausdorffMeasure_le_variationMeasure_preimage hn inter_subset_right).trans
    (measure_mono (preimage_mono inter_subset_left))

/-- **The measure of the reduced boundary is at most the perimeter**, localized. Let `E` have
dimension `n ≥ 2`, with Lebesgue measure. For every open `U ⊆ Ω`, the part of the reduced boundary
of `s` in `Ω` lying in `U` satisfies `μHE[n - 1] (∂*s ∩ U) ≤ P(s; U)`. -/
theorem euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter (hn : 2 ≤ finrank ℝ E)
    (hU : U ≤ Ω) :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ U) ≤ perimeter volume U s := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume ∧ ∀ K, IsCompact K →
      K ⊆ Ω → ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞
  · rw [perimeter_def, ← variationMeasure_preimage_coe h.1 h.2 hU]
    exact (euclideanHausdorffMeasure_le_variationMeasure_preimage hn inter_subset_left).trans
      (measure_mono (preimage_mono inter_subset_right))
  · simp [reducedBoundary_eq_empty_of_not h]

/-- **The measure of the reduced boundary is at most the perimeter.** Let `E` have dimension
`n ≥ 2`, with Lebesgue measure. The reduced boundary of `s` in `Ω` satisfies
`μHE[n - 1] (∂*s) ≤ P(s; Ω)`. -/
theorem euclideanHausdorffMeasure_reducedBoundary_le_perimeter (hn : 2 ≤ finrank ℝ E) :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s) ≤ perimeter volume Ω s := by
  simpa only [inter_eq_left.2 reducedBoundary_subset] using
    euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter (s := s) hn le_rfl

/-- **The reduced boundary has locally finite Hausdorff measure.** Let `E` have dimension `n ≥ 2`,
with Lebesgue measure. For every compact `K ⊆ Ω`, the part of the reduced boundary of `s` in `Ω`
lying in `K` has finite `(n - 1)`-dimensional measure. -/
theorem euclideanHausdorffMeasure_reducedBoundary_inter_lt_top (hn : 2 ≤ finrank ℝ E) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ K) < ∞ := by
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe] using hKΩ)
  exact (euclideanHausdorffMeasure_le_variationMeasure_preimage hn inter_subset_left).trans_lt
    ((measure_mono (preimage_mono inter_subset_right)).trans_lt hK'.measure_lt_top)

end TauCeti
