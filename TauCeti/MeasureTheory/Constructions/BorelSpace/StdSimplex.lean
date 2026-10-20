/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.ConvexSpace.NNReal
public import TauCeti.MeasureTheory.MeasurableSpace.StdSimplex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The Borel structure of the finite nonnegative-real simplex

The weight-coordinate measurable structure on `Convexity.StdSimplex ℝ≥0 ι` agrees with the
Borel structure of its coordinate topology when `ι` is finite. Thus continuous families of
probability vectors also give measurable parameters for finite laws.
-/

public section

open MeasureTheory
open scoped NNReal

namespace Convexity.StdSimplex

variable {ι : Type*} [Finite ι]

/-- The coordinate measurable structure of the finite nonnegative-real simplex is Borel. -/
instance instBorelSpaceNNReal : BorelSpace (StdSimplex ℝ≥0 ι) where
  measurable_eq := by
    simp only [instMeasurableSpace, borel_comap, Finsupp.equivFunOnFinite_apply,
      ← BorelSpace.measurable_eq (α := ι → ℝ≥0)]

end Convexity.StdSimplex
