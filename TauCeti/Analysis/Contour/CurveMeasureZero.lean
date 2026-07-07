/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Curve images in `ℂ` have Lebesgue measure zero

The image of a Lipschitz map from a subset of the line `ℝ` into `ℂ` has two-dimensional Lebesgue
measure zero: a Lipschitz map does not increase Hausdorff dimension, so the image sits in dimension
`≤ 1 < 2` and is null for the `2`-dimensional Hausdorff measure, which on `ℂ` agrees (up to a
constant) with Lebesgue volume. Consequently any open nonempty subset of `ℂ` contains a point off
the image.

This is the prerequisite that supplies the interior evaluation point off the curve in the Cauchy
integral formula step of the homology Cauchy theorem: a piecewise-`C¹` contour is Lipschitz on its
(compact) parameter interval, so its image is null and cannot cover a nonempty open set.

## Main results

* `Contour.volume_image_zero_of_lipschitzOnWith` — a curve Lipschitz on `s ⊆ ℝ` has null image.
* `Contour.exists_mem_notMem_image_of_isOpen_of_lipschitzOnWith` — an open nonempty set contains a
  point off the image of such a curve.

## Provenance

Adapted from `CurveMeasureZero.lean` in the AINTLIB `LeanModularForms` development, generalized from
a globally Lipschitz map to one Lipschitz on the parameter set and re-expressed on a raw function.
-/

public section

noncomputable section

namespace TauCeti.Contour

open MeasureTheory Measure Set

/-- The `2`-dimensional Hausdorff measure of the image of `s ⊆ ℝ` under a map `f : ℝ → ℂ` that is
Lipschitz on `s` is zero, since `μH[2]` vanishes on `ℝ` (`finrank ℝ ℝ = 1 < 2`). -/
theorem hausdorffMeasure_two_image_zero_of_lipschitzOnWith {K : NNReal} {f : ℝ → ℂ} {s : Set ℝ}
    (hf : LipschitzOnWith K f s) : μH[2] (f '' s) = 0 := by
  have h0 : (μH[2] : Measure ℝ) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt (by simp [Module.finrank_self])
  have h_le := hf.hausdorffMeasure_image_le (d := 2) (by norm_num)
  rw [h0] at h_le
  simpa using h_le

/-- The Lebesgue volume in `ℂ` of the image of `s ⊆ ℝ` under a map Lipschitz on `s` is zero: volume
is a Haar measure on the `2`-dimensional real space `ℂ`, hence absolutely continuous with respect to
`μH[2]`, which is null on the image. -/
theorem volume_image_zero_of_lipschitzOnWith {K : NNReal} {f : ℝ → ℂ} {s : Set ℝ}
    (hf : LipschitzOnWith K f s) : volume (f '' s) = 0 := by
  have h_finrank : ((Module.finrank ℝ ℂ : ℕ) : ℝ) = 2 := by
    exact_mod_cast Complex.finrank_real_complex
  have h_haar : (μH[2] : Measure ℂ).IsAddHaarMeasure := by
    rw [show (2 : ℝ) = ((Module.finrank ℝ ℂ : ℕ) : ℝ) from h_finrank.symm]
    exact isAddHaarMeasure_hausdorffMeasure
  have h_ac : (volume : Measure ℂ).AbsolutelyContinuous (μH[2]) :=
    absolutelyContinuous_isAddHaarMeasure _ _
  exact h_ac (hausdorffMeasure_two_image_zero_of_lipschitzOnWith hf)

/-- For an open nonempty `U ⊆ ℂ` and `f : ℝ → ℂ` Lipschitz on `s ⊆ ℝ`, some point of `U` lies off
the image `f '' s`: that image has measure zero, so it cannot cover the positive-measure set `U`. -/
theorem exists_mem_notMem_image_of_isOpen_of_lipschitzOnWith {U : Set ℂ} (hU : IsOpen U)
    (hU_ne : U.Nonempty) {K : NNReal} {f : ℝ → ℂ} {s : Set ℝ} (hf : LipschitzOnWith K f s) :
    ∃ w ∈ U, w ∉ f '' s := by
  by_contra! h
  have h_zero : volume U ≤ 0 := by
    rw [← volume_image_zero_of_lipschitzOnWith hf]
    exact measure_mono h
  exact (h_zero.trans_lt (hU.measure_pos _ hU_ne)).false

end TauCeti.Contour
