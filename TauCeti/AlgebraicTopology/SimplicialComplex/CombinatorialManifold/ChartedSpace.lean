/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Boundary
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Combinatorial
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# Charted spaces from combinatorial manifolds

The weak realization of a positive-dimensional combinatorial manifold carries a charted-space
structure modelled on the Euclidean half-space. At an interior vertex, its combinatorial-sphere
link gives an open Euclidean ball chart; the standard open embedding of Euclidean space into the
interior of the half-space turns this into a half-space chart. At a boundary vertex, its
combinatorial-ball link directly gives an open half-ball chart. The open vertex stars cover the
realization, so choosing one such chart at each point produces an atlas.

This is the topological assembly step in the comparison between link-condition combinatorial
manifolds and chart-based PL manifolds. Piecewise-linear compatibility of the resulting vertex
charts is a separate result.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2--3.
-/

public section

noncomputable section

open AbstractSimplicialComplex Metric Set Topology
open scoped Manifold

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι} {v : ι} {n : ℕ}

/-! ### Interior vertex charts -/

/-- A combinatorial-sphere link gives a chart on the weak realization whose source is the open
vertex star and whose target is the open unit ball. -/
theorem IsCombinatorialSphere.exists_openPartialHomeomorph_openStar_ball
    (h : IsCombinatorialSphere (link K.toPreAbstractSimplicialComplex {v}) n) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanSpace ℝ (Fin (n + 1))),
      c.source = openStarRealization K v := by
  obtain ⟨e, -⟩ := h.exists_homeomorph_openStar_ball
  let U : Set (EuclideanSpace ℝ (Fin (n + 1))) := ball 0 1
  have hU : IsOpen U := isOpen_ball
  let : Nonempty U := ⟨⟨0, by simp [U]⟩⟩
  let j : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin (n + 1))) :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let f := e.toOpenPartialHomeomorph.trans j
  let c := f.lift_openEmbedding (K.isOpen_openStarRealization v).isOpenEmbedding_subtypeVal
  refine ⟨c, ?_⟩
  simp only [OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, PartialHomeomorph.toFun_eq_coe,
    OpenPartialHomeomorph.coe_toPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_self, image_univ,
    Subtype.range_coe_subtype, mem_openStarRealization, c, f, j]
  ext x
  exact (K.mem_openStarRealization).symm

/-! ### A common half-space model -/

/-- Every vertex of a positive-dimensional combinatorial manifold supplies a half-space chart
whose source is its open star. Interior charts land in the interior of the half-space; boundary
charts are the half-ball charts coming from combinatorial-ball links. -/
theorem IsCombinatorialManifold.exists_openPartialHomeomorph_openStar_halfSpace
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    (hv : ({v} : Finset ι) ∈ K) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)),
      c.source = openStarRealization K v := by
  rcases (isCombinatorialManifold_succ_iff.mp h) hv with hsphere | hball
  · obtain ⟨c, hc⟩ := hsphere.exists_openPartialHomeomorph_openStar_ball
    let j : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))
        (EuclideanHalfSpace (n + 1)) :=
      (TauCeti.EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
    refine ⟨c.trans j, ?_⟩
    simp [hc, j]
  · obtain ⟨c, hc, -, -, -⟩ :=
      hball.exists_openPartialHomeomorph_openStar_halfBall
    exact ⟨c, hc⟩

/-- Every point of the realization of a positive-dimensional combinatorial manifold lies in the
source of a half-space chart obtained from an open vertex star. -/
theorem IsCombinatorialManifold.exists_openPartialHomeomorph_mem_source
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
    (x : Realization K) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (n + 1)), x ∈ c.source := by
  obtain ⟨v, hx⟩ := K.exists_mem_openStarRealization x
  have hv : ({v} : Finset ι) ∈ K :=
    singleton_mem_of_mem (support_mem K x)
      ((K.mem_openStarRealization_iff_mem_support).mp hx)
  obtain ⟨c, hc⟩ := h.exists_openPartialHomeomorph_openStar_halfSpace hv
  exact ⟨c, hc.symm ▸ hx⟩

/-! ### The vertex-chart atlas -/

/-- The charted-space structure on the weak realization of a positive-dimensional combinatorial
manifold. Its preferred charts are chosen from the interior or boundary vertex charts supplied by
the link condition. -/
@[instance_reducible] noncomputable def IsCombinatorialManifold.realizationChartedSpace
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    ChartedSpace (EuclideanHalfSpace (n + 1)) (Realization K) where
  atlas := range fun x => Classical.choose (h.exists_openPartialHomeomorph_mem_source x)
  chartAt x := Classical.choose (h.exists_openPartialHomeomorph_mem_source x)
  mem_chart_source x := Classical.choose_spec (h.exists_openPartialHomeomorph_mem_source x)
  chart_mem_atlas _ := mem_range_self _

/-- The weak realization of a positive-dimensional combinatorial manifold is a topological
manifold with boundary, for the charted-space structure assembled from its vertex links. -/
theorem IsCombinatorialManifold.realization_isManifold
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    IsManifold (𝓡∂ (n + 1)) 0 (Realization K) := by
  let := h.realizationChartedSpace
  infer_instance

end PreAbstractSimplicialComplex
