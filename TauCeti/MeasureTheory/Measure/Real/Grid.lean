/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measures decomposed across uniform real grids

A positive-width uniform grid partitions the real line into countably many
measurable, pairwise-disjoint cells. Countable additivity expresses the measure
of the whole real line as the sum of the masses of these cells.

The decomposition applies to arbitrary measures, including those of infinite total
mass. It is useful when computing spectral-measure masses cell by cell.
-/

public section

open MeasureTheory

namespace TauCeti

/-- The mass of the real line is the sum of its masses on positive-width grid cells. -/
theorem measure_univ_eq_tsum_gridCell (μ : Measure ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    μ Set.univ = ∑' k : ℤ, μ (gridCell ε k) := by
  rw [← iUnion_gridCell hε]
  exact measure_iUnion (pairwise_disjoint_gridCell ε)
    (fun k => measurableSet_gridCell ε k)

end TauCeti
