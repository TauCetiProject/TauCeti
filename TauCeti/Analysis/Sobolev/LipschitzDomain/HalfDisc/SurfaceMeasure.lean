/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic

/-!
# Surface measure on the flat segment of the half-disc

The flat segment `TauCeti.halfDiscFlatSegment r = {x | ‖x‖ ≤ r ∧ x.fst = 0}` of the frontier of
the half-disc is the image of the real interval `[-r, r]` under the isometry `t ↦ (0, t)`. This
file identifies surface measure on it, normalized one-dimensional Euclidean Hausdorff measure,
with the image of Lebesgue measure on `[-r, r]`, and draws the consequences used by the trace
condition on the flat segment.

## Main declarations

* `TauCeti.euclideanHausdorffMeasure_restrict_halfDiscFlatSegment`: surface measure on the flat
  segment is Lebesgue measure on `[-r, r]`.
* `TauCeti.euclideanHausdorffMeasure_halfDiscFlatSegment`: the flat segment has length `2 r`.
* `TauCeti.eqOn_halfDiscFlatSegment_of_ae_eq`: continuous functions that agree almost everywhere
  on the flat segment agree on it.
* `TauCeti.restrict_frontier_restrict_halfDiscFlatSegment`: surface measure on the frontier of
  the half-disc, restricted to the flat segment, is surface measure on the flat segment.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set

namespace TauCeti

/-- **Surface measure on the flat segment.** Normalized one-dimensional Euclidean Hausdorff
measure on the flat segment of the half-disc is the image of Lebesgue measure on `[-r, r]` under
the isometry `t ↦ (0, t)`. -/
theorem euclideanHausdorffMeasure_restrict_halfDiscFlatSegment (r : ℝ) :
    (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r) =
      (volume.restrict (Icc (-r) r)).map fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t) := by
  have hι := WithLp.isometry_toLp_zero_prod (p := 2) (α := ℝ) (β := ℝ)
  have hvol : (μHE[1] : Measure ℝ) = volume := by
    simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  have hpre : (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) ⁻¹' halfDiscFlatSegment r = Icc (-r) r := by
    rw [← image_Icc_eq_halfDiscFlatSegment, hι.injective.preimage_image]
  rw [← hpre, ← Measure.restrict_map hι.continuous.measurable
    (measurableSet_halfDiscFlatSegment r), ← hvol, hι.map_euclideanHausdorffMeasure,
    Measure.restrict_restrict (measurableSet_halfDiscFlatSegment r), inter_eq_left.2]
  rw [← image_Icc_eq_halfDiscFlatSegment]
  exact image_subset_range _ _

/-- The flat segment of the half-disc of radius `r` has length `2 r`. -/
theorem euclideanHausdorffMeasure_halfDiscFlatSegment (r : ℝ) :
    (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))) (halfDiscFlatSegment r) = ENNReal.ofReal (2 * r) := by
  have hι := WithLp.isometry_toLp_zero_prod (p := 2) (α := ℝ) (β := ℝ)
  rw [← Measure.restrict_apply_univ, euclideanHausdorffMeasure_restrict_halfDiscFlatSegment,
    Measure.map_apply hι.continuous.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Real.volume_Icc]
  ring_nf

/-- **Continuous functions are determined by their values almost everywhere on the flat
segment.** For `0 < r`, two functions continuous on the flat segment that agree almost everywhere
for surface measure on it agree at every point of it. -/
theorem eqOn_halfDiscFlatSegment_of_ae_eq {Y : Type*} [TopologicalSpace Y] [T2Space Y] {r : ℝ}
    (hr : 0 < r) {f g : WithLp 2 (ℝ × ℝ) → Y}
    (hf : ContinuousOn f (halfDiscFlatSegment r)) (hg : ContinuousOn g (halfDiscFlatSegment r))
    (hfg : f =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r)] g) :
    EqOn f g (halfDiscFlatSegment r) := by
  have hι := WithLp.isometry_toLp_zero_prod (p := 2) (α := ℝ) (β := ℝ)
  have hmaps : MapsTo (fun t : ℝ => WithLp.toLp 2 ((0 : ℝ), t)) (Icc (-r) r)
      (halfDiscFlatSegment r) := by
    rw [← image_Icc_eq_halfDiscFlatSegment]
    exact mapsTo_image _ _
  rw [euclideanHausdorffMeasure_restrict_halfDiscFlatSegment] at hfg
  have hEq := Measure.eqOn_Icc_of_ae_eq volume (by linarith : -r ≠ r)
    (ae_of_ae_map (p := fun y => f y = g y) hι.continuous.aemeasurable hfg)
    (hf.comp hι.continuous.continuousOn hmaps) (hg.comp hι.continuous.continuousOn hmaps)
  rw [← image_Icc_eq_halfDiscFlatSegment]
  rintro _ ⟨t, ht, rfl⟩
  exact hEq ht

/-- Surface measure on the frontier of the half-disc, restricted to the flat segment, is surface
measure on the flat segment. This identifies the measure of the codomain of
`TauCeti.W1p.halfDiscFlatTrace`. -/
theorem restrict_frontier_restrict_halfDiscFlatSegment (r : ℝ) :
    ((μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict
        (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))).restrict (halfDiscFlatSegment r) =
      (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict (halfDiscFlatSegment r) := by
  rw [Measure.restrict_restrict (measurableSet_halfDiscFlatSegment r), finrank_self]
  rcases lt_or_ge 0 r with hr | hr
  · rw [inter_eq_left.2 (halfDiscFlatSegment_subset_frontier hr)]
  · have h0 : (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))) (halfDiscFlatSegment r) = 0 := by
      rw [euclideanHausdorffMeasure_halfDiscFlatSegment, ENNReal.ofReal_eq_zero]
      linarith
    rw [Measure.restrict_eq_zero.2 h0, Measure.restrict_eq_zero.2 (measure_mono_null
      inter_subset_left h0)]

end TauCeti
