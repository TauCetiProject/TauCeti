/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import TauCeti.Analysis.BoundedVariation.OneDimensional.Perimeter
public import TauCeti.Analysis.BoundedVariation.Hyperplane
public import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Checks for the weighted perimeter with weight zero

With the weight `0`, the weighted perimeter is the Euclidean perimeter
(`TauCeti.weightedPerimeter_zero_weight`). On `ℝ` the half-line `(0, ∞)` has perimeter `1` and the
interval `(0, 1)` has perimeter `2`; in `ℝ²` the half-plane `{x | x₀ < 0}` has infinite perimeter,
its boundary being a whole line.
-/

open MeasureTheory Set TopologicalSpace
open scoped RealInnerProductSpace

namespace TauCeti.Examples.WeightedPerimeter

/-- With weight `0` on `ℝ`, the half-line `(0, ∞)` has perimeter `1`. -/
example : weightedPerimeter (0 : ℝ → ℝ) ⊤ (Ioi 0) = 1 := by
  have hν : ‖(-1 : ℝ)‖ = 1 := by simp
  have hset : Ioi (0 : ℝ) = {x : ℝ | ⟪x, -1⟫ < 0} := by
    ext x
    simp
  have hbdry : ((⊤ : Opens ℝ) : Set ℝ) ∩ {x : ℝ | ⟪x, -1⟫ = 0} = {0} := by
    ext x
    simp
  rw [weightedPerimeter_zero_weight, hset, perimeter_setOf_inner_lt hν, hbdry]
  simp

/-- With weight `0` on `ℝ`, the interval `(0, 1)` has perimeter `2`. -/
example : weightedPerimeter (0 : ℝ → ℝ) ⊤ (Ioo 0 1) = 2 := by
  rw [weightedPerimeter_zero_weight, Real.perimeter_Ioo zero_lt_one]

/-- With weight `0` on `ℝ²`, the half-plane `{x | x₀ < 0}` has infinite perimeter. -/
example : weightedPerimeter (0 : EuclideanSpace ℝ (Fin 2) → ℝ) ⊤ {x | x 0 < 0} = ⊤ := by
  set ν : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  have hν : ‖ν‖ = 1 := by simp [ν]
  have hset : {x : EuclideanSpace ℝ (Fin 2) | x 0 < 0} = {x | ⟪x, ν⟫ < 0} := by
    ext x
    simp [ν, EuclideanSpace.inner_single_right]
  rw [weightedPerimeter_zero_weight, hset, perimeter_setOf_inner_lt hν, Opens.coe_top,
    univ_inter]
  exact euclideanHausdorffMeasure_setOf_inner_eq_eq_top (by simp) hν 0

end TauCeti.Examples.WeightedPerimeter
