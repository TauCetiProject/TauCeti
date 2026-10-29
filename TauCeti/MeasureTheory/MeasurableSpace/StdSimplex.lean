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

The inverse weight map extends to all weight vectors by choosing a fallback simplex point.
Its measurability under topological hypotheses is established in the Borel simplex file.

Mathlib's topology on the simplex is stated over a ring and does not reach coefficients such as
`ℝ≥0`; the induced σ-algebra needs no topology.

## Main declarations

* `Convexity.StdSimplex.instMeasurableSpace` — the σ-algebra induced by `StdSimplex.weights`;
* `Convexity.StdSimplex.measurable_toFun_comp_weights` — the weight vector is measurable;
* `Convexity.StdSimplex.measurable_iff_toFun_comp_weights` — measurability into the simplex is
  measurability of the weight vector;
* `Convexity.StdSimplex.extendWeights` — an inverse weight map with a chosen fallback.
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

namespace Convexity.StdSimplex

variable {R ι : Type*} [PartialOrder R] [Semiring R]

/-- A simplex point is determined by its weight vector. -/
theorem injective_toFun_comp_weights :
    Function.Injective fun p : StdSimplex R ι ↦ (p.weights : ι → R) :=
  fun _ _ h ↦ StdSimplex.ext (DFunLike.coe_injective h)

/-- Read a weight vector as a simplex point when it lies in the simplex, using `p` elsewhere.
This supplies probability parameters for mixtures supported on a simplex. -/
noncomputable def extendWeights (p : StdSimplex R ι) (w : ι → R) : StdSimplex R ι :=
  Function.extend (fun q : StdSimplex R ι ↦ (q.weights : ι → R)) id (fun _ ↦ p) w

/-- The inverse weight map is extended with constant fallback value `p`. -/
theorem extendWeights_def (p : StdSimplex R ι) :
    p.extendWeights =
      Function.extend (fun q : StdSimplex R ι ↦ (q.weights : ι → R)) id (fun _ ↦ p) := (rfl)

/-- Extending the inverse of the weight embedding recovers every simplex point. -/
@[simp]
theorem extendWeights_weights (p q : StdSimplex R ι) :
    p.extendWeights q.weights = q :=
  injective_toFun_comp_weights.extend_apply _ _ q

/-- Extending the inverse weight map preserves every vector in the simplex. -/
@[simp]
theorem weights_extendWeights_of_mem_range (p : StdSimplex R ι) {w : ι → R}
    (hw : w ∈ Set.range (fun q : StdSimplex R ι ↦ (q.weights : ι → R))) :
    ⇑(p.extendWeights w).weights = w := by
  obtain ⟨q, rfl⟩ := hw
  rw [extendWeights_weights]

/-- A vector outside the simplex is sent to the chosen fallback point. -/
@[simp]
theorem extendWeights_of_notMem_range (p : StdSimplex R ι) {w : ι → R}
    (hw : w ∉ Set.range (fun q : StdSimplex R ι ↦ (q.weights : ι → R))) :
    p.extendWeights w = p :=
  Function.extend_apply' _ _ _ hw

end Convexity.StdSimplex
