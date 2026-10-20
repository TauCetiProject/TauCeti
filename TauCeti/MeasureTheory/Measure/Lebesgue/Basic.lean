/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue measure on the real line

An affine map `x ↦ a * x + c` of the real line scales Lebesgue measure by `|a|`; this holds for
arbitrary sets, including `a = 0`, and gives the self-similarity of the pre-Cantor sets.

Replacing two subsets of the real line by open centered intervals of the same respective
volumes can only decrease the volume of their one-sided difference. The inequality uses
Mathlib's extended-radius balls and `Real.volume_eball`, and allows zero and infinite volumes.
It supplies the sectionwise contraction inequality for Steiner symmetrization.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The affine map `x ↦ a * x + c` scales the Lebesgue measure of every set by `|a|`. -/
theorem volume_image_mul_add (a c : ℝ) (s : Set ℝ) :
    volume ((fun x ↦ a * x + c) '' s) = ENNReal.ofReal |a| * volume s := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using measure_mono_null (image_subset_iff.2 fun x _ ↦ by simp)
      (measure_singleton (μ := volume) c)
  · rw [image_eq_preimage_of_inverse (f := fun x ↦ a * x + c) (g := fun y ↦ a⁻¹ * (y + -c))
      (fun x ↦ by field_simp; ring) (fun y ↦ by field_simp; ring),
      show (fun y ↦ a⁻¹ * (y + -c)) ⁻¹' s = (· + -c) ⁻¹' ((a⁻¹ * ·) ⁻¹' s) from rfl,
      measure_preimage_add_right, Real.volume_preimage_mul_left (inv_ne_zero ha), inv_inv]

/-- Centering intervals can only decrease the length of a one-sided difference. -/
theorem volume_eball_sdiff_le (s u : Set ℝ) :
    volume (Metric.eball (0 : ℝ) (volume s / 2) \ Metric.eball 0 (volume u / 2)) ≤
      volume (s \ u) := by
  have hlength (a : ℝ≥0∞) : volume (Metric.eball (0 : ℝ) (a / 2)) = a := by
    rw [Real.volume_eball]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  rcases le_total (volume s) (volume u) with h | h
  · rw [sdiff_eq_empty.mpr (Metric.eball_subset_eball (ENNReal.div_le_div_right h 2)),
      measure_empty]
    exact bot_le
  · by_cases hu : volume u = ∞
    · have hs : volume s = ∞ := top_le_iff.mp (hu ▸ h)
      simp [hu, hs]
    · rw [measure_sdiff (Metric.eball_subset_eball (ENNReal.div_le_div_right h 2))
        Metric.isOpen_eball.measurableSet.nullMeasurableSet (by rwa [hlength]), hlength, hlength]
      exact le_measure_sdiff

end TauCeti
