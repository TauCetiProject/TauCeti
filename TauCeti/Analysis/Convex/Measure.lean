/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Measure

/-!
# Almost every point of a convex set is interior

The frontier of a convex set in a finite-dimensional real normed space is null for any additive
Haar measure (`Convex.addHaar_frontier`). Consequently, almost every point of the set is in its
interior.
-/

public section

open MeasureTheory MeasureTheory.Measure Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ] {s : Set E}

/-- Almost every point of a convex set in a finite-dimensional real normed space is an interior
point, since the frontier of the set is null for every additive Haar measure. -/
theorem Convex.ae_mem_interior (hs : Convex ℝ s) : ∀ᵐ x ∂μ, x ∈ s → x ∈ interior s :=
  (interior_ae_eq_of_null_frontier (hs.addHaar_frontier μ)).symm.le
