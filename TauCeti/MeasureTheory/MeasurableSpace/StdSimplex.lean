/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The measurable structure of the standard simplex

A point of the standard simplex `StdSimplex ℝ≥0 ι` is determined by its weight vector
`ι → ℝ≥0`. This file gives the simplex the σ-algebra induced by that weight vector,
so that a probability vector is a measurable parameter: a map into the simplex is measurable
exactly when its weight-vector map is, and the weight vector itself is measurable.

Mathlib's topology on the simplex is stated over a ring and does not apply to `ℝ≥0`; the induced
σ-algebra needs no topology.

## Main declarations

* `Convexity.StdSimplex.instMeasurableSpace` — the σ-algebra induced by `StdSimplex.weights`;
* `Convexity.StdSimplex.measurable_weights` — the weight vector is measurable;
* `Convexity.StdSimplex.measurable_iff_weights` — measurability into the simplex is measurability
  of the weight vector.
-/

public section

open MeasureTheory
open scoped NNReal

namespace Convexity.StdSimplex

variable {ι : Type*}

/-- The σ-algebra on the standard simplex induced by its weight vector. -/
instance instMeasurableSpace : MeasurableSpace (StdSimplex ℝ≥0 ι) :=
  MeasurableSpace.comap (fun p : StdSimplex ℝ≥0 ι => (p.weights : ι → ℝ≥0)) inferInstance

/-- The weight vector of a simplex point is measurable. -/
@[fun_prop]
theorem measurable_weights : Measurable fun p : StdSimplex ℝ≥0 ι => (p.weights : ι → ℝ≥0) :=
  comap_measurable _

/-- A map into the simplex is measurable iff its weight-vector map is. -/
theorem measurable_iff_weights {δ : Type*} [MeasurableSpace δ] {f : δ → StdSimplex ℝ≥0 ι} :
    Measurable f ↔ Measurable fun x => ((f x).weights : ι → ℝ≥0) := by
  rw [measurable_iff_comap_le]
  simp only [instMeasurableSpace, MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.symm

end Convexity.StdSimplex
