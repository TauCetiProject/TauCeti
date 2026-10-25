/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The Lévy–Prokhorov distance between pushforward measures

Mathlib's `MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt` compares the masses of a set and
of its thickening under two measures on the same space. This file restates it for the images
`μ.map T` and `ν.map S` of measures on two measurable spaces `X` and `Y` under a.e.-measurable maps
into a common extended pseudometric space `Z`, in terms of sets of `X` and `Y`.

## Main declarations

* `TauCeti.measure_le_of_levyProkhorovEDist_map_lt`: if `d_LP (T_# μ, S_# ν) < δ`, then
  `μ A ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ` for every set `A ⊆ X`, measurable or not.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace Z]
  [MeasurableSpace Z] [OpensMeasurableSpace Z] {μ : Measure X} {ν : Measure Y} {δ : ℝ≥0∞}

/-- A Lévy–Prokhorov bound between images of `μ` and `ν` in a common space `Z` moves every set
`A ⊆ X` into the points of `Y` whose image is close to the image of `A`. -/
theorem measure_le_of_levyProkhorovEDist_map_lt {T : X → Z} {S : Y → Z}
    (hT : AEMeasurable T μ) (hS : AEMeasurable S ν)
    (h : levyProkhorovEDist (μ.map T) (ν.map S) < δ) (A : Set X) :
    μ A ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ := by
  rcases eq_or_ne δ ∞ with rfl | hδ
  · exact le_top.trans_eq (add_top _).symm
  calc μ A ≤ μ.map T (closure (T '' A)) :=
        (Measure.le_map_apply_image hT A).trans (measure_mono subset_closure)
    _ ≤ ν.map S (thickening δ.toReal (closure (T '' A))) + δ :=
        left_measure_le_of_levyProkhorovEDist_lt h isClosed_closure.measurableSet
    _ = ν (S ⁻¹' thickening δ.toReal (T '' A)) + δ := by
        rw [thickening_closure, Measure.map_apply_of_aemeasurable hS
          isOpen_thickening.measurableSet]
    _ ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ := by
        refine add_le_add_left (measure_mono fun y hy ↦ ?_) _
        rw [mem_preimage, mem_thickening_iff_exists_edist_lt] at hy
        obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hy
        rw [edist_comm, ENNReal.ofReal_toReal hδ] at hxy
        exact ⟨x, hx, hxy⟩

end TauCeti
