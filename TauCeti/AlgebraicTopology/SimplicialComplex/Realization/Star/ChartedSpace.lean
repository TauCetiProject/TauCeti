/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Assembling an atlas of vertex-star charts

Charts on all open vertex stars give a charted-space structure on the weak polyhedron.
The preferred chart at a point uses a vertex with positive barycentric coordinate.
In particular, the preferred chart at a vertex is its own vertex-star chart.

The atlas is exactly the supplied family. Consequently, checking its compatibility
with a structure groupoid amounts to checking the transitions between these charts.
The model space and the vertex type are arbitrary; neither finiteness nor countability
is required. Local sphere or ball models can supply the charts, independently of their
subsequent smooth or piecewise-linear compatibility.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 2–3 (vertex-star atlases).
-/

public section

noncomputable section

open Set

namespace AbstractSimplicialComplex

variable {ι H : Type*} [TopologicalSpace H]
  (K : AbstractSimplicialComplex ι) (e : ι → OpenPartialHomeomorph (Realization K) H)
  (hs : ∀ v, (e v).source = K.openStarRealization v)

/-- Assemble charts whose sources are all the open vertex stars into an atlas on the
existing weak realization topology. At each point, use a vertex with positive coordinate. -/
@[instance_reducible]
def starChartedSpace : ChartedSpace H (Realization K) where
  atlas := range e
  chartAt x := e (K.exists_mem_openStarRealization x).choose
  mem_chart_source x := by
    rw [hs]
    exact (K.exists_mem_openStarRealization x).choose_spec
  chart_mem_atlas x := mem_range_self _

/-- The atlas consists exactly of the supplied vertex-star charts. -/
@[simp]
theorem starChartedSpace_atlas :
    @atlas H _ (Realization K) _ (K.starChartedSpace e hs) = range e := (rfl)

/-- The preferred chart uses a vertex whose coordinate at the point is positive. -/
theorem starChartedSpace_chartAt (x : Realization K) :
    @chartAt H _ (Realization K) _ (K.starChartedSpace e hs) x =
      e (K.exists_mem_openStarRealization x).choose := (rfl)

/-- At a vertex, the preferred chart is the supplied chart for that vertex. -/
@[simp]
theorem starChartedSpace_chartAt_vertex (v : ι) :
    @chartAt H _ (Realization K) _ (K.starChartedSpace e hs) (vertex K v) = e v := by
  rw [starChartedSpace_chartAt]
  have hv := (K.exists_mem_openStarRealization (vertex K v)).choose_spec
  have heq : (K.exists_mem_openStarRealization (vertex K v)).choose = v := by
    simpa only [vertex_val, Finsupp.support_single v one_ne_zero, Finset.mem_singleton] using
      K.mem_openStarRealization_iff_mem_support.mp hv
  rw [heq]

end AbstractSimplicialComplex
