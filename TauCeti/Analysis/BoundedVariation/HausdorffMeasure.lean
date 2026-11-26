/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary.Basic
public import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.LowerDensityEstimates

/-!
# Hausdorff measure on the reduced boundary is at most the perimeter measure

Let `Ω` be an open set of a finite-dimensional real inner product space `E` of dimension `n`,
with Lebesgue measure, and let `s ⊆ E`. This file proves that the normalized
`(n - 1)`-dimensional Hausdorff measure `μHE[n - 1]` of a set of points of the reduced boundary
`∂*s` of `s` in `Ω` is at most its perimeter measure `|Dχ_s|`:

`μHE[n - 1] (A) ≤ |Dχ_s| (A)`     for every `A ⊆ ∂*s`

(`TauCeti.euclideanHausdorffMeasure_le_variationMeasure_preimage`), with the sharp constant one
and with no measurability of `A`. In measure form, `μHE[n - 1]⌊∂*s ≤ |Dχ_s|`
(`TauCeti.euclideanHausdorffMeasure_restrict_reducedBoundary_le_map_variationMeasure`). This is one
of the two inequalities of the identity `|Dχ_s| = μHE[n - 1]⌊∂*s` in De Giorgi's structure theorem.
The reverse inequality uses the rectifiability of the reduced boundary and is not proved here.

The comparison rests on the lower density of `|Dχ_s|` at points of `∂*s`: for `n ≥ 2`,
`|Dχ_s| (closedBall x r) / (ωₙ₋₁ rⁿ⁻¹) → 1` as `r → 0⁺`, where `ωₙ₋₁ rⁿ⁻¹` is the Lebesgue measure
of a closed ball of radius `r` in `ℝⁿ⁻¹`
(`TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`), and for `n = 1`, where
`μHE[0]` is counting measure, `1 ≤ |Dχ_s| (closedBall x r)` for small `r`
(`TauCeti.eventually_addHaarScalarFactor_le_variationMeasure_closedBall_of_finrank_eq_one`, whose
factor `Measure.addHaarScalarFactor volume volume` is `1`).

Consequences:

* `TauCeti.euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter` and
  `TauCeti.euclideanHausdorffMeasure_reducedBoundary_le_perimeter`: the `(n - 1)`-dimensional
  measure of the reduced boundary is at most the perimeter, `μHE[n - 1] (∂*s ∩ U) ≤ P(s; U)` for
  every open `U`; in particular `μHE[n - 1] (∂*s) ≤ P(s; Ω)`.
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

open MeasureTheory TopologicalSpace Set Module Filter Metric
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω U : Opens E} {s : Set E}

/-- **Hausdorff measure on the reduced boundary is at most the perimeter measure.** Let `E` have
dimension `n`, with Lebesgue measure. Every set `A` of points of the reduced boundary `∂*s` of
`s` in `Ω` satisfies `μHE[n - 1] (A) ≤ |Dχ_s| (A)`. No measurability of `A` is assumed. -/
theorem euclideanHausdorffMeasure_le_variationMeasure_preimage {A : Set E}
    (hA : A ⊆ reducedBoundary volume Ω s) :
    μHE[finrank ℝ E - 1] A ≤
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) := by
  have hAΩ : A ∩ range ((↑) : Ω → E) = A := by
    rw [Subtype.range_coe]
    exact inter_eq_left.2 (hA.trans reducedBoundary_subset)
  conv_lhs => rw [← hAΩ, ← isometry_subtypeVal.euclideanHausdorffMeasure_preimage]
  refine ENNReal.le_of_forall_lt_one_mul_le fun t ht => ?_
  refine Measure.mul_euclideanHausdorffMeasure_le_measure _ _ fun y hy => ?_
  -- The outer normal is a unit vector, so `E` is not zero-dimensional.
  have h0 : finrank ℝ E ≠ 0 := fun h0 => by
    have := finrank_zero_iff.1 h0
    simpa [Subsingleton.elim (outerNormal volume Ω s y) 0] using norm_outerNormal (hA hy)
  obtain hn | hn := (Nat.one_le_iff_ne_zero.2 h0).eq_or_lt
  · -- In dimension one, `ω₀ r ^ 0 = 1` and every small ball has perimeter measure at least one.
    have hvol {r : ℝ} (hr : 0 < r) :
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) r) = 1 := by
      rw [← hn, Nat.sub_self, volume_euclideanSpace_eq_dirac,
        Measure.dirac_apply_of_mem (mem_closedBall_self hr.le)]
    refine (((eventually_addHaarScalarFactor_le_variationMeasure_closedBall_of_finrank_eq_one
      hn.symm (hA hy)).and self_mem_nhdsWithin).mono fun r ⟨hr, hr0⟩ => ?_).frequently
    rw [Measure.addHaarScalarFactor_self, ENNReal.coe_one] at hr
    rw [hvol hr0, mul_one, ← Subtype.preimage_closedBall]
    exact ht.le.trans hr
  -- The density of `|Dχ_s|` at `y` is one, so it eventually exceeds `t < 1`.
  have hdens := tendsto_variationMeasure_closedBall_div_volume_closedBall hn (hA hy)
  refine ((hdens.eventually (lt_mem_nhds ht)).mono fun r hr => ?_).frequently
  rw [← Subtype.preimage_closedBall]
  exact ENNReal.mul_le_of_le_div hr.le

/-- **Hausdorff measure on the reduced boundary is at most the perimeter measure**, measure form.
Let `E` have dimension `n`, with Lebesgue measure. The restriction of `μHE[n - 1]` to the
reduced boundary of `s` in `Ω` is at most the perimeter measure `|Dχ_s|`, viewed as a measure on
the ambient space. -/
theorem euclideanHausdorffMeasure_restrict_reducedBoundary_le_map_variationMeasure :
    μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s) ≤
      (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) := by
  refine Measure.le_iff.2 fun N hN => ?_
  rw [Measure.restrict_apply hN, Measure.map_apply measurable_subtypeVal hN]
  exact (euclideanHausdorffMeasure_le_variationMeasure_preimage inter_subset_right).trans
    (measure_mono (preimage_mono inter_subset_left))

/-- **The measure of the reduced boundary is at most the perimeter**, localized. Let `E` have
dimension `n`, with Lebesgue measure. For every open `U`, the part of the reduced boundary
of `s` in `Ω` lying in `U` satisfies `μHE[n - 1] (∂*s ∩ U) ≤ P(s; U)`. -/
theorem euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ U) ≤ perimeter volume U s := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume ∧ ∀ K, IsCompact K →
      K ⊆ Ω → ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞
  · refine le_trans ?_ (perimeter_mono (inf_le_left : U ⊓ Ω ≤ U))
    rw [perimeter_def, ← variationMeasure_preimage_coe h.1 h.2 inf_le_right]
    exact (euclideanHausdorffMeasure_le_variationMeasure_preimage inter_subset_left).trans
      (measure_mono (preimage_mono fun x hx => ⟨hx.2, reducedBoundary_subset hx.1⟩))
  · simp [reducedBoundary_eq_empty_of_not h]

/-- **The measure of the reduced boundary is at most the perimeter.** Let `E` have dimension
`n`, with Lebesgue measure. The reduced boundary of `s` in `Ω` satisfies
`μHE[n - 1] (∂*s) ≤ P(s; Ω)`. -/
theorem euclideanHausdorffMeasure_reducedBoundary_le_perimeter :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s) ≤ perimeter volume Ω s := by
  simpa only [inter_eq_left.2 reducedBoundary_subset] using
    euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter (Ω := Ω) (U := Ω) (s := s)

/-- **The reduced boundary has locally finite Hausdorff measure.** Let `E` have dimension `n`, with
Lebesgue measure. For every compact `K ⊆ Ω`, the part of the reduced boundary of `s` in `Ω`
lying in `K` has finite `(n - 1)`-dimensional measure. -/
theorem euclideanHausdorffMeasure_reducedBoundary_inter_lt_top {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ K) < ∞ := by
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe] using hKΩ)
  exact (euclideanHausdorffMeasure_le_variationMeasure_preimage inter_subset_left).trans_lt
    ((measure_mono (preimage_mono inter_subset_right)).trans_lt hK'.measure_lt_top)

end TauCeti
