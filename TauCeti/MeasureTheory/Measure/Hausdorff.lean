/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Lipschitz images of low-dimensional sets have measure zero

A Lipschitz map does not raise Hausdorff dimension, so the image of a set under a map that is
Lipschitz on it is null for any Hausdorff measure `μH[d]` whose exponent `d` exceeds the real
dimension of the source. Specialized to a map `ℝ → ℂ`, the image is null for the `2`-dimensional
Hausdorff measure, hence for Lebesgue volume on `ℂ` (the two are mutually absolutely continuous
Haar measures on the `2`-dimensional real space `ℂ`). Consequently a subset of `ℂ` of positive
volume — in particular any open nonempty set — contains a point off the image.

The `ℝ → ℂ` results are the prerequisite that supplies the interior evaluation point off a curve in
the Cauchy integral formula: a rectifiable (e.g. piecewise-`C¹`) curve is Lipschitz on its compact
parameter interval, so its image cannot cover a nonempty open set.

## Main results

* `TauCeti.hausdorffMeasure_image_zero_of_lipschitzOnWith` — the general Hausdorff-null statement.
* `TauCeti.volume_image_zero_of_lipschitzOnWith` — a curve `ℝ → ℂ` Lipschitz on `s` has null image.
* `TauCeti.exists_mem_notMem_image_of_volume_pos` and
  `TauCeti.exists_mem_notMem_image_of_isOpen_of_lipschitzOnWith` — a positive-volume (resp. open
  nonempty) set contains a point off the image.

## Provenance

Adapted from `CurveMeasureZero.lean` in the AINTLIB `LeanModularForms` development, generalized to a
map Lipschitz on the parameter set and to an arbitrary low-dimensional source.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set

/-- The `d`-dimensional Hausdorff measure of the image of `s` under a map `f` Lipschitz on `s` is
zero whenever the real dimension of the source is `< d`: a Lipschitz map does not raise Hausdorff
dimension, and `μH[d]` already vanishes on the low-dimensional source. -/
theorem hausdorffMeasure_image_zero_of_lipschitzOnWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Y : Type*} [EMetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {K : NNReal} {f : E → Y} {s : Set E} {d : ℝ}
    (hd : (Module.finrank ℝ E : ℝ) < d) (hf : LipschitzOnWith K f s) :
    μH[d] (f '' s) = 0 := by
  have h0 : (μH[d] : Measure E) = 0 := Real.hausdorffMeasure_of_finrank_lt (by exact_mod_cast hd)
  have h_le := hf.hausdorffMeasure_image_le ((Nat.cast_nonneg _).trans hd.le)
  rw [h0] at h_le
  simpa using h_le

/-- The Lebesgue volume in `ℂ` of the image of `s ⊆ ℝ` under a map Lipschitz on `s` is zero: the
image is `μH[2]`-null (source dimension `1 < 2`), and volume is a Haar measure on the plane `ℂ`,
hence absolutely continuous with respect to `μH[2]`. -/
theorem volume_image_zero_of_lipschitzOnWith {K : NNReal} {f : ℝ → ℂ} {s : Set ℝ}
    (hf : LipschitzOnWith K f s) : volume (f '' s) = 0 := by
  have h_finrank : ((Module.finrank ℝ ℂ : ℕ) : ℝ) = 2 := by
    exact_mod_cast Complex.finrank_real_complex
  have h_null : μH[2] (f '' s) = 0 :=
    hausdorffMeasure_image_zero_of_lipschitzOnWith (by norm_num [Module.finrank_self]) hf
  have h_haar : (μH[2] : Measure ℂ).IsAddHaarMeasure := by
    rw [← h_finrank]; exact isAddHaarMeasure_hausdorffMeasure
  exact absolutelyContinuous_isAddHaarMeasure _ _ h_null

/-- For a set `U ⊆ ℂ` of positive Lebesgue measure and `f : ℝ → ℂ` Lipschitz on `s ⊆ ℝ`, some point
of `U` lies off the null image `f '' s`. -/
theorem exists_mem_notMem_image_of_volume_pos {U : Set ℂ} (hU : 0 < volume U) {K : NNReal}
    {f : ℝ → ℂ} {s : Set ℝ} (hf : LipschitzOnWith K f s) : ∃ w ∈ U, w ∉ f '' s := by
  by_contra! h
  have hle : volume U ≤ 0 := by
    rw [← volume_image_zero_of_lipschitzOnWith hf]; exact measure_mono h
  exact absurd hle (not_le.mpr hU)

/-- For an open nonempty `U ⊆ ℂ` and `f : ℝ → ℂ` Lipschitz on `s ⊆ ℝ`, some point of `U` lies off
the image `f '' s`. -/
theorem exists_mem_notMem_image_of_isOpen_of_lipschitzOnWith {U : Set ℂ} (hU : IsOpen U)
    (hU_ne : U.Nonempty) {K : NNReal} {f : ℝ → ℂ} {s : Set ℝ} (hf : LipschitzOnWith K f s) :
    ∃ w ∈ U, w ∉ f '' s :=
  exists_mem_notMem_image_of_volume_pos (hU.measure_pos volume hU_ne) hf

end TauCeti
