/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# The measurable structure of the standard simplex

A point of the standard simplex `StdSimplex R ι` is determined by its weight vector `ι → R`.
This file gives the simplex the σ-algebra induced by that weight vector, for any coefficient type
`R` carrying a measurable structure, so that a probability vector is a measurable parameter: the
weight vector is measurable, and a map into the simplex is measurable exactly when its
weight-vector map is.

Mathlib's topology on the simplex is stated over a ring and does not reach coefficients such as
`ℝ≥0`; the induced σ-algebra needs no topology.

## Main declarations

* `Convexity.StdSimplex.instMeasurableSpace` — the σ-algebra induced by `StdSimplex.weights`;
* `Convexity.StdSimplex.measurable_toFun_comp_weights` — the weight vector is measurable;
* `Convexity.StdSimplex.measurable_iff_toFun_comp_weights` — measurability into the simplex is
  measurability of the weight vector.
-/

public section

open MeasureTheory

namespace Convexity.StdSimplex

variable {R ι : Type*} [LE R] [AddCommMonoid R] [One R] [MeasurableSpace R]

/-- The σ-algebra on the standard simplex induced by its weight vector. -/
instance instMeasurableSpace : MeasurableSpace (StdSimplex R ι) :=
  MeasurableSpace.comap (fun p : StdSimplex R ι => (p.weights : ι → R)) inferInstance

/-- The weight vector of a simplex point is measurable. -/
@[fun_prop]
theorem measurable_toFun_comp_weights : Measurable fun p : StdSimplex R ι => (p.weights : ι → R) :=
  comap_measurable _

/-- A map into the simplex is measurable iff its weight-vector map is. -/
theorem measurable_iff_toFun_comp_weights {δ : Type*} [MeasurableSpace δ] {f : δ → StdSimplex R ι} :
    Measurable f ↔ Measurable fun x => ((f x).weights : ι → R) :=
  measurable_comap_iff

end Convexity.StdSimplex
