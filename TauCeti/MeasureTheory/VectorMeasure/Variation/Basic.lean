/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import TauCeti.MeasureTheory.VectorMeasure.Operations

/-!
# Variation of vector measures: null sets and continuous linear maps

The variation `|μ|` of a vector measure `μ` controls where `μ` lives. A vector measure is
absolutely continuous with respect to a positive measure `ν` exactly when its variation is, and
removing a set of zero variation does not change the values of `μ`.

Applying a continuous linear map `φ` to the values of a vector measure multiplies its variation
by at most `‖φ‖₊`. In particular the image has finite variation when `μ` has, and its variation is
absolutely continuous with respect to `|μ|`.

## Main declarations

* `MeasureTheory.VectorMeasure.variation_absolutelyContinuous_iff`: `|μ| ≪ ν ↔ μ ≪ᵥ ν`.
* `MeasureTheory.VectorMeasure.apply_diff_of_variation_eq_zero`: `μ (s \ t) = μ s` when
  `|μ| t = 0`.
* `MeasureTheory.VectorMeasure.variation_mapRangeL_le`: `|φ ∘ μ| ≤ ‖φ‖₊ • |μ|`.
* `MeasureTheory.VectorMeasure.variation_mapRangeL_absolutelyContinuous`: `|φ ∘ μ| ≪ |μ|`.

## References

* J. Diestel and J. J. Uhl, Jr., *Vector Measures*, Chapter I, §1.
-/

public section

open scoped NNReal ENNReal

namespace MeasureTheory.VectorMeasure

section NullSets

variable {X V : Type*} [MeasurableSpace X] [TopologicalSpace V] [ENormedAddCommMonoid V]
  [T2Space V] {μ : VectorMeasure X V}

/-- The variation of a vector measure is absolutely continuous with respect to a positive measure
`ν` exactly when the vector measure itself vanishes on the `ν`-null sets. -/
theorem variation_absolutelyContinuous_iff {ν : Measure X} :
    μ.variation ≪ ν ↔ μ ≪ᵥ ν.toENNRealVectorMeasure := by
  refine ⟨fun h => AbsolutelyContinuous.mk fun s hs hνs => ?_, fun h s hνs => ?_⟩
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hνs
    exact eNorm_eq_zero.1 <| nonpos_iff_eq_zero.1 <|
      (eNorm_measure_le_variation μ s).trans (h hνs).le
  · -- Pass to a measurable `ν`-null superset, all of whose measurable subsets are `μ`-null.
    have ht : MeasurableSet (toMeasurable ν s) := measurableSet_toMeasurable ν s
    refine measure_mono_null (subset_toMeasurable ν s) <|
      (variation_apply_eq_zero ht).2 fun t hts htm => h ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable htm]
    exact measure_mono_null hts (by rwa [measure_toMeasurable])

/-- Removing a measurable set of zero variation from a measurable set does not change the value of
a vector measure. -/
theorem apply_diff_of_variation_eq_zero {s t : Set X} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : μ.variation t = 0) : μ (s \ t) = μ s := by
  have h0 : μ (t ∩ s) = 0 :=
    (variation_apply_eq_zero ht).1 h _ Set.inter_subset_left (ht.inter hs)
  rw [← of_add_of_sdiff (ht.inter hs) hs Set.inter_subset_right, h0, zero_add,
    Set.sdiff_inter_self_eq_sdiff]

end NullSets

variable {X F F' 𝕜 : Type*} [MeasurableSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Applying a continuous linear map to the values of a vector measure multiplies its variation
by at most the operator norm of the map. -/
theorem variation_mapRangeL_le (φ : F →L[𝕜] F') (μ : VectorMeasure X F) :
    (mapRangeL φ μ).variation ≤ ‖φ‖₊ • μ.variation := by
  refine variation_le_of_forall_eNorm_le fun s _ => ?_
  rw [mapRangeL_apply, _root_.smul_apply, ENNReal.smul_def, smul_eq_mul]
  refine (φ.le_opENorm _).trans ?_
  rw [eNorm_eq_nnNorm φ]
  gcongr
  exact eNorm_measure_le_variation μ s

/-- Applying a continuous linear map to the values of a vector measure gives a vector measure whose
variation is absolutely continuous with respect to the original variation. -/
theorem variation_mapRangeL_absolutelyContinuous (φ : F →L[𝕜] F') (μ : VectorMeasure X F) :
    (mapRangeL φ μ).variation ≪ μ.variation :=
  (Measure.absolutelyContinuous_of_le (variation_mapRangeL_le φ μ)).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)

/-- Applying a continuous linear map to the values of a vector measure of finite variation gives a
vector measure of finite variation. -/
instance isFiniteMeasure_variation_mapRangeL (φ : F →L[𝕜] F') (μ : VectorMeasure X F)
    [IsFiniteMeasure μ.variation] : IsFiniteMeasure (mapRangeL φ μ).variation :=
  isFiniteMeasure_of_le _ (variation_mapRangeL_le φ μ)

end MeasureTheory.VectorMeasure
