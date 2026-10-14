/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ConstantSpeed
public import TauCeti.Geometry.Euclidean.Volume.Measure
public import TauCeti.MeasureTheory.Measure.Haar.Hausdorff

/-!
# Constant speed and the length of curves of bounded variation

Constant speed bounds distances by elapsed parameter time. Mathlib's natural parameterization
therefore shows that the image of any curve of locally bounded variation has Hausdorff dimension
at most one. In particular this applies to absolutely continuous planar curves.

The same factorization bounds the one-dimensional Hausdorff measure of the trace of a curve by
its total variation, `H¹(f '' s) ≤ eVariationOn f s`, both for Mathlib's raw Hausdorff measure
`μH[1]` and for the Euclidean normalization `μHE[1]`. No continuity, injectivity, or finiteness
hypothesis is needed: the bound is trivial when the variation is infinite.

## Main results

* `LocallyBoundedVariationOn.dimH_image_le_one`: a curve of locally bounded variation has a trace
  of Hausdorff dimension at most one.
* `eVariationOn.hausdorffMeasure_image_le`: `μH[1] (f '' s) ≤ eVariationOn f s`.
* `eVariationOn.euclideanHausdorffMeasure_image_le`: `μHE[1] (f '' s) ≤ eVariationOn f s`.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A curve with constant speed is Lipschitz with that speed as its Lipschitz constant. -/
theorem HasConstantSpeedOnWith.lipschitzOnWith {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} {l : ℝ≥0} (hf : HasConstantSpeedOnWith f s l) :
    LipschitzOnWith l f s := by
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [edist_comm] using this hy hx (le_of_not_ge hxy)
  have hdist := eVariationOn.edist_le f (s := s ∩ Icc x y)
    ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  rw [hf hx hy] at hdist
  have hmul : ENNReal.ofReal ((l : ℝ) * (y - x)) =
      (l : ENNReal) * ENNReal.ofReal (y - x) := by
    exact (ENNReal.ofReal_mul l.prop).trans (by simp)
  simpa only [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    using hdist.trans_eq hmul

/-- The extended diameter of the set of cumulative variations from a base point of `s` is at most
the total variation on `s`. -/
theorem variationOnFromTo.ediam_image_le {α E : Type*} [LinearOrder α] [TopologicalSpace E]
    [WeakPseudoEMetricSpace E] (f : α → E) {s : Set α} {a : α} (ha : a ∈ s) :
    Metric.ediam (variationOnFromTo f s a '' s) ≤ eVariationOn f s := by
  by_cases hf : BoundedVariationOn f s
  swap
  · rw [BoundedVariationOn, not_ne_iff] at hf
    exact hf ▸ le_top
  refine Metric.ediam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [edist_dist, Real.dist_eq, variationOnFromTo.sub_right hf.locallyBoundedVariationOn ha hx hy,
    ← ENNReal.ofReal_toReal hf]
  exact ENNReal.ofReal_le_ofReal (variationOnFromTo.abs_le_eVariationOn hf)

/-- A curve of locally bounded variation on `s` factors, on `s`, through its natural
parameterization restricted to the set of cumulative variations from a base point. -/
theorem LocallyBoundedVariationOn.image_subset_image_naturalParameterization {α E : Type*}
    [LinearOrder α] [EMetricSpace E] {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (ha : a ∈ s) :
    f '' s ⊆ naturalParameterization f s a '' (variationOnFromTo f s a '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨variationOnFromTo f s a x, ⟨x, hx, rfl⟩,
    edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf ha hx)⟩

/-- The image of a curve of locally bounded variation has Hausdorff dimension at most one,
because its natural parameterization is Lipschitz on a subset of the real line. -/
theorem LocallyBoundedVariationOn.dimH_image_le_one {α E : Type*} [LinearOrder α]
    [MetricSpace E] {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) :
    dimH (f '' s) ≤ 1 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  let φ := naturalParameterization f s a
  let v := variationOnFromTo f s a
  have hφ : LipschitzOnWith 1 φ (v '' s) :=
    (has_unit_speed_naturalParameterization f hf ha).lipschitzOnWith
  calc
    dimH (f '' s) ≤ dimH (φ '' (v '' s)) :=
      dimH_mono (hf.image_subset_image_naturalParameterization ha)
    _ ≤ dimH (v '' s) := hφ.dimH_image_le
    _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = 1 := Real.dimH_univ

namespace eVariationOn

variable {α E : Type*} [LinearOrder α] [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The one-dimensional Hausdorff measure of the image of `s` under `f` is at most the total
variation of `f` on `s`. In particular, the trace of a rectifiable curve has Hausdorff length at
most the length of the curve. -/
theorem hausdorffMeasure_image_le (f : α → E) (s : Set α) :
    μH[1] (f '' s) ≤ eVariationOn f s := by
  by_cases hf : BoundedVariationOn f s
  swap
  · rw [BoundedVariationOn, not_ne_iff] at hf
    exact hf ▸ le_top
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  let φ := naturalParameterization f s a
  let v := variationOnFromTo f s a
  have hφ : LipschitzOnWith 1 φ (v '' s) :=
    (has_unit_speed_naturalParameterization f hf.locallyBoundedVariationOn ha).lipschitzOnWith
  calc
    μH[1] (f '' s) ≤ μH[1] (φ '' (v '' s)) :=
      measure_mono (hf.locallyBoundedVariationOn.image_subset_image_naturalParameterization ha)
    _ ≤ μH[1] (v '' s) := by
      simpa using hφ.hausdorffMeasure_image_le zero_le_one
    _ = volume (v '' s) := by rw [hausdorffMeasure_real]
    _ ≤ Metric.ediam (v '' s) := Real.volume_le_diam _
    _ ≤ eVariationOn f s := variationOnFromTo.ediam_image_le f ha

/-- The Euclidean one-dimensional Hausdorff measure of the image of `s` under `f` is at most the
total variation of `f` on `s`. In particular, the trace of a rectifiable curve has
one-dimensional Euclidean Hausdorff measure at most the length of the curve. -/
theorem euclideanHausdorffMeasure_image_le (f : α → E) (s : Set α) :
    μHE[1] (f '' s) ≤ eVariationOn f s := by
  rw [Measure.euclideanHausdorffMeasure_one]
  exact hausdorffMeasure_image_le f s

end eVariationOn

/-- The image of a curve of locally bounded variation has zero additive Haar measure in every
finite-dimensional real normed space of dimension greater than one. -/
theorem LocallyBoundedVariationOn.addHaar_image_eq_zero {α E : Type*} [LinearOrder α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1 < Module.finrank ℝ E) : μ (f '' s) = 0 :=
  addHaar_eq_zero_of_dimH_lt_finrank μ
    (hf.dimH_image_le_one.trans_lt (by exact_mod_cast hd))
