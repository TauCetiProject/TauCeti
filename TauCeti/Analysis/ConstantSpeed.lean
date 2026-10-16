/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ConstantSpeed
public import TauCeti.MeasureTheory.Measure.Haar.Hausdorff

/-!
# Constant speed and the dimension of curves of bounded variation

Constant speed bounds distances by elapsed parameter time. Mathlib's natural parameterization
therefore shows that the image of any curve of locally bounded variation has Hausdorff dimension
at most one. In particular this applies to absolutely continuous planar curves.
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
  have himage : f '' s ⊆ φ '' (v '' s) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨v x, ⟨x, hx, rfl⟩,
      edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf ha hx)⟩
  calc
    dimH (f '' s) ≤ dimH (φ '' (v '' s)) := dimH_mono himage
    _ ≤ dimH (v '' s) := hφ.dimH_image_le
    _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ _)
    _ = 1 := Real.dimH_univ

/-- The image of a curve of locally bounded variation has zero additive Haar measure in every
finite-dimensional real normed space of dimension greater than one. -/
theorem LocallyBoundedVariationOn.addHaar_image_eq_zero {α E : Type*} [LinearOrder α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : α → E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1 < Module.finrank ℝ E) : μ (f '' s) = 0 :=
  addHaar_eq_zero_of_dimH_lt_finrank μ
    (hf.dimH_image_le_one.trans_lt (by exact_mod_cast hd))
