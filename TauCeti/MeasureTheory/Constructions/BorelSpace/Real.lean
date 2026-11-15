/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.EMetricSpace.Weak
public import TauCeti.Order.Interval.Set.RealGrid

/-!
# Measurability of extended distances and uniform real grids

## Extended distance on `ℝ≥0∞`

`ℝ≥0∞` carries the extended distance `edist a b = max (a - b) (b - a)` of a weak extended metric
space, which is not jointly continuous for the order topology, so Mathlib's `measurable_edist`
does not apply to it. The distance is nevertheless Borel measurable, because truncated
subtraction is. This lets the Wasserstein distance be used for laws on `[0, ∞]`, such as the
distribution of an extended-valued random variable.

## Uniform real grids

Each half-open real grid cell is Borel measurable, so it can be used in
measurable decompositions of the real line, including spectral measures.
-/

public section

open MeasureTheory
open scoped ENNReal

/-- The extended distance on `ℝ≥0∞` is jointly measurable. -/
@[fun_prop]
theorem ENNReal.measurable_edist : Measurable fun z : ℝ≥0∞ × ℝ≥0∞ ↦ edist z.1 z.2 := by
  simp only [ENNReal.edist_eq_max]
  fun_prop

namespace Real

/-- Each half-open interval cell of a real grid is Borel measurable. -/
@[simp, measurability]
theorem measurableSet_gridCell (ε : ℝ) (k : ℤ) :
    MeasurableSet (gridCell ε k) := by
  rw [gridCell_eq_Ico]
  exact measurableSet_Ico

end Real
