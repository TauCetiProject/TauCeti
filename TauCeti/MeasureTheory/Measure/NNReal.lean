/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue measure on the nonnegative half-line

`TauCeti.nnvolume` is the pullback of real Lebesgue measure to `ℝ≥0`. Its pushforward
under the inclusion into `ℝ` is Lebesgue measure restricted to `[0,∞)`. It is locally
finite and atomless; in particular, counting `(0,t]` or `[0,t]` gives the same length.

This explicit reference measure is useful for intensities of temporal random measures,
without installing a global `MeasureSpace ℝ≥0` instance.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- Lebesgue measure on `ℝ≥0`, obtained by pulling back real Lebesgue measure. -/
noncomputable def nnvolume : Measure ℝ≥0 :=
  (volume : Measure ℝ).comap ((↑) : ℝ≥0 → ℝ)

/-- The defining pullback formula for half-line Lebesgue measure. -/
theorem nnvolume_def : nnvolume = (volume : Measure ℝ).comap ((↑) : ℝ≥0 → ℝ) := (rfl)

/-- Half-line Lebesgue measure is real Lebesgue measure on the image, even for
nonmeasurable sets. -/
theorem nnvolume_apply (s : Set ℝ≥0) : nnvolume s = volume (((↑) : ℝ≥0 → ℝ) '' s) :=
  (MeasurableEmbedding.subtype_coe measurableSet_Ici).comap_apply volume s

/-- Inclusion carries half-line Lebesgue measure to real Lebesgue measure restricted
to the nonnegative half-line. -/
@[simp]
theorem map_coe_nnvolume : nnvolume.map ((↑) : ℝ≥0 → ℝ) = volume.restrict (Ici 0) := by
  have he := NNReal.isEmbedding_coe.measurableEmbedding
    (NNReal.range_coe ▸ measurableSet_Ici)
  rw [nnvolume_def, he.map_comap, NNReal.range_coe]

/-- Compact sets have finite half-line Lebesgue measure. -/
instance : IsFiniteMeasureOnCompacts nnvolume :=
  IsFiniteMeasureOnCompacts.comap' volume NNReal.continuous_coe
    (NNReal.isEmbedding_coe.measurableEmbedding (NNReal.range_coe ▸ measurableSet_Ici))

/-- Half-line Lebesgue measure has no atoms, including at zero. -/
instance : NullSingletonClass nnvolume := by
  refine ⟨fun x => ?_⟩
  simp [nnvolume_apply]

/-- The length of a closed initial interval is its right endpoint. -/
@[simp]
theorem nnvolume_Iic (t : ℝ≥0) : nnvolume (Iic t) = (t : ℝ≥0∞) := by
  rw [nnvolume_apply, NNReal.image_coe_Iic, Real.volume_Icc]
  simp

/-- A half-open interval has its usual length; the formula is zero for reversed endpoints. -/
@[simp]
theorem nnvolume_Ioc (s t : ℝ≥0) : nnvolume (Ioc s t) = ((t - s : ℝ≥0) : ℝ≥0∞) := by
  rw [nnvolume_apply, NNReal.image_coe_Ioc, Real.volume_Ioc]
  simp [ENNReal.ofReal_sub]

/-- Changing either endpoint convention leaves the length unchanged. -/
@[simp]
theorem nnvolume_Icc (s t : ℝ≥0) : nnvolume (Icc s t) = ((t - s : ℝ≥0) : ℝ≥0∞) := by
  rw [nnvolume_apply, NNReal.image_coe_Icc, Real.volume_Icc]
  simp [ENNReal.ofReal_sub]

/-- Open intervals have their usual length, also when the left endpoint is zero. -/
@[simp]
theorem nnvolume_Ioo (s t : ℝ≥0) : nnvolume (Ioo s t) = ((t - s : ℝ≥0) : ℝ≥0∞) := by
  rw [nnvolume_apply, NNReal.image_coe_Ioo, Real.volume_Ioo]
  simp [ENNReal.ofReal_sub]

/-- Left-closed, right-open intervals have their usual length. -/
@[simp]
theorem nnvolume_Ico (s t : ℝ≥0) : nnvolume (Ico s t) = ((t - s : ℝ≥0) : ℝ≥0∞) := by
  rw [nnvolume_apply, NNReal.image_coe_Ico, Real.volume_Ico]
  simp [ENNReal.ofReal_sub]

end TauCeti
