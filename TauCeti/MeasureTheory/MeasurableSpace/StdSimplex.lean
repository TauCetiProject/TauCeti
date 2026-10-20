/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The measurable structure of the standard simplex

A point of the standard simplex `StdSimplex R ι` is determined by its weight vector `ι → R`.
This file gives the simplex the σ-algebra induced by that weight vector, for any coefficient type
`R` carrying a measurable structure, so that a probability vector is a measurable parameter: the
weight vector is measurable, and a map into the simplex is measurable exactly when its
weight-vector map is.

For finite coordinate types with topologically measurable coefficients, the weight map is a
measurable embedding. Its inverse extends measurably to all weight vectors by choosing a
fallback simplex point; this permits mixing distributions against simplex-supported laws.

Mathlib's topology on the simplex is stated over a ring and does not reach coefficients such as
`ℝ≥0`; the induced σ-algebra needs no topology.

## Main declarations

* `Convexity.StdSimplex.instMeasurableSpace` — the σ-algebra induced by `StdSimplex.weights`;
* `Convexity.StdSimplex.measurable_toFun_comp_weights` — the weight vector is measurable;
* `Convexity.StdSimplex.measurable_iff_toFun_comp_weights` — measurability into the simplex is
  measurability of the weight vector;
* `Convexity.StdSimplex.extendWeights` — a measurable inverse weight map with a chosen fallback.
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

variable {R ι : Type*} [PartialOrder R] [Semiring R] [MeasurableSpace R]

/-- The weight vector embeds a finite standard simplex as a measurable subset of the
coordinate space. -/
theorem measurableEmbedding_toFun_comp_weights [TopologicalSpace R] [OpensMeasurableSpace R]
    [OrderClosedTopology R] [ContinuousAdd R] [SecondCountableTopology R] [Finite ι] :
    MeasurableEmbedding fun p : StdSimplex R ι ↦ (p.weights : ι → R) := by
  let _ := Fintype.ofFinite ι
  refine MeasurableEmbedding.iff_comap_eq.mpr ⟨?_, rfl, ?_⟩
  · intro p q hpq
    exact StdSimplex.ext (DFunLike.coe_injective hpq)
  · rw [range_toFun_comp_weights]
    exact (MeasurableSet.iInter fun i ↦
      (isClosed_Ici.preimage (continuous_apply i)).measurableSet).inter
        (isClosed_eq (by fun_prop) continuous_const).measurableSet

/-- Read a weight vector as a simplex point when it lies in the simplex, using `p` elsewhere.
This supplies measurable probability parameters for mixtures supported on a simplex. -/
noncomputable def extendWeights (p : StdSimplex R ι) (w : ι → R) : StdSimplex R ι :=
  Function.extend (fun q : StdSimplex R ι ↦ (q.weights : ι → R)) id (fun _ ↦ p) w

omit [MeasurableSpace R] in
/-- Extending the inverse of the weight embedding recovers every simplex point. -/
@[simp]
theorem extendWeights_weights (p q : StdSimplex R ι) :
    p.extendWeights q.weights = q := by
  have hinj : Function.Injective fun q : StdSimplex R ι ↦ (q.weights : ι → R) :=
    fun _ _ h ↦ StdSimplex.ext (DFunLike.coe_injective h)
  exact hinj.extend_apply _ _ q

omit [MeasurableSpace R] in
/-- A vector outside the simplex is sent to the chosen fallback point. -/
@[simp]
theorem extendWeights_of_not_mem_range (p : StdSimplex R ι) {w : ι → R}
    (hw : w ∉ Set.range (fun q : StdSimplex R ι ↦ (q.weights : ι → R))) :
    p.extendWeights w = p :=
  Function.extend_apply' _ _ _ hw

/-- The extension of the inverse weight map is measurable, including outside the simplex. -/
@[fun_prop]
theorem measurable_extendWeights [TopologicalSpace R] [OpensMeasurableSpace R]
    [OrderClosedTopology R] [ContinuousAdd R] [SecondCountableTopology R] [Finite ι]
    (p : StdSimplex R ι) : Measurable p.extendWeights :=
  measurableEmbedding_toFun_comp_weights.measurable_extend measurable_id measurable_const

end Convexity.StdSimplex
