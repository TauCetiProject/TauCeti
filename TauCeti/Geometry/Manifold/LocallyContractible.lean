/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Local contractibility of manifolds

Every point of a real manifold, possibly with boundary or corners, has a basis of contractible
neighbourhoods. The model space `H` of a real model with corners `I` is homeomorphic to the convex
set `range I`, whose intersections with balls are convex and hence contractible
(`ModelWithCorners.stronglyLocallyContractibleSpace`), and a charted space inherits this property
from its model through the inverse charts (`ChartedSpace.stronglyLocallyContractibleSpace`). The
circle is an instance (`instStronglyLocallyContractibleSpaceCircle`).

In particular every point of a manifold has arbitrarily small open neighbourhoods whose inclusion
is nullhomotopic, which is what makes small neighbourhoods of finitely many points categorical in
the sense of Lusternik and Schnirelmann.
-/

public section

open Set Topology

/-- The model space of a real model with corners is strongly locally contractible: the model
embeds it onto the convex set `range I`, in which every ball cuts out a convex, hence contractible,
neighbourhood. -/
theorem ModelWithCorners.stronglyLocallyContractibleSpace {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) :
    StronglyLocallyContractibleSpace H :=
  .of_bases (fun y ↦ I.isClosedEmbedding.isInducing.basis_nhds (Metric.nhds_basis_ball (x := I y)))
    fun y r hr ↦ by
      have hconv : Convex ℝ (I '' (I ⁻¹' Metric.ball (I y) r)) := by
        rw [image_preimage_eq_inter_range]
        exact (convex_ball _ _).inter I.convex_range
      exact (I.isClosedEmbedding.isEmbedding.homeomorphImage _).contractibleSpace_iff.mpr
        (hconv.contractibleSpace ⟨I y, y, Metric.mem_ball_self hr, rfl⟩)

/-- A charted space modelled on a strongly locally contractible space is strongly locally
contractible: the inverse chart at a point carries the contractible neighbourhoods of its
coordinate inside the chart target onto contractible neighbourhoods of the point. -/
theorem ChartedSpace.stronglyLocallyContractibleSpace (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [StronglyLocallyContractibleSpace H] :
    StronglyLocallyContractibleSpace M := by
  refine .of_bases
    (p := fun x s ↦ s ∈ 𝓝 (chartAt H x x) ∧ ContractibleSpace s ∧ s ⊆ (chartAt H x).target)
    (s := fun x s ↦ (chartAt H x).symm '' s) (fun x ↦ ?_) fun x s ⟨_, hs, hst⟩ ↦ ?_
  · rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact (contractible_subset_basis (chartAt H x).open_target (mem_chart_target H x)).map _
  · exact ((chartAt H x).symm.homeomorphOfImageSubsetSource (by simpa using hst)
      rfl).contractibleSpace_iff.mp hs

/-- The circle is strongly locally contractible, as a manifold modelled on
`EuclideanSpace ℝ (Fin 1)`. -/
instance instStronglyLocallyContractibleSpaceCircle : StronglyLocallyContractibleSpace Circle :=
  have := (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).stronglyLocallyContractibleSpace
  ChartedSpace.stronglyLocallyContractibleSpace (EuclideanSpace ℝ (Fin 1)) Circle
