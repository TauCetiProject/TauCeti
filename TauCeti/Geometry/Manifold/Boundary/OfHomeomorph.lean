/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# The boundary of a manifold from a homeomorphism of the model boundary

Let `I : ModelWithCorners 𝕜 E H` be a model with corners on a finite-dimensional space, and `M` a
charted space modelled on `H`. Every chart of `M`, in the atlas or not, reads the boundary points of
`M` as the points that `I` sends to the frontier of its range
(`ModelWithCorners.mem_boundary_iff_mem_frontier_range_of_finiteDimensional`): this is the
topological invariance of the boundary, and it needs no condition on the transition maps. So a
homeomorphism `φ` from the boundary `{z : H // I z ∈ frontier (range I)}` of the model onto a
space `F` turns every chart of `M` into a chart of the boundary `I.boundary M` with values in `F`:
restrict the chart to the boundary and follow it by `φ`. These charts make the boundary of `M` a
charted space modelled on `F` (`ModelWithCorners.boundaryChartedSpaceOfHomeomorph`).

The construction also takes a map `π : H → F` extending `φ`, so that the charts read every point of
their domain through `π`, without a membership proof. The charts themselves are built with
`OpenPartialHomeomorph.subtypeCoord`. The boundary charted spaces `TauCeti.boundaryChartedSpace`
in `TauCeti/Geometry/Manifold/Boundary/Charts.lean`, `TauCeti.halfSpaceBoundaryChartedSpace` in
`TauCeti/Geometry/Manifold/Boundary/ProductHalfSpace.lean` and
`TauCeti.euclideanQuadrantBoundaryChartedSpace` in `TauCeti/Geometry/Manifold/Corners/Boundary.lean`
are instances of this construction.

## Main definitions

* `ModelWithCorners.boundaryChartedSpaceOfHomeomorph`: the charted-space structure on
  `I.boundary M` induced by a homeomorphism of the model boundary onto `F`.

## Main results

* `ModelWithCorners.boundaryChartedSpaceOfHomeomorph_atlas` and the
  `boundaryChartedSpaceOfHomeomorph_chartAt_*` lemmas: the atlas of the boundary and the source,
  target, values and inverse of its charts.
-/

public section

open Set

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {F : Type*} [TopologicalSpace F]
  {φ : {z : H // I z ∈ frontier (range I)} ≃ₜ F} {π : H → F}
  {e : OpenPartialHomeomorph M H}

/-- The inverse of the homeomorphism of the model boundary, read in the target of a chart of `M`,
is the reading of a boundary point. -/
private theorem symm_symm_mem_boundary {y : F} (hy : (φ.symm y : H) ∈ e.target) :
    e.symm (φ.symm y) ∈ I.boundary M := by
  rw [mem_boundary_iff_mem_frontier_range_of_finiteDimensional (e.map_target hy), e.right_inv hy]
  exact (φ.symm y).property

/-- The homeomorphism of the model boundary recovers the chart value of a boundary point. -/
private theorem symm_apply_apply_of_mem_boundary
    (hπ : ∀ z : {z : H // I z ∈ frontier (range I)}, π z = φ z) {x : M} (hx : x ∈ e.source)
    (hxb : x ∈ I.boundary M) : (φ.symm (π (e x)) : H) = e x := by
  have h := hπ ⟨e x, (mem_boundary_iff_mem_frontier_range_of_finiteDimensional hx).1 hxb⟩
  rw [h, φ.symm_apply_apply]

omit [FiniteDimensional 𝕜 E] in
/-- An extension of the homeomorphism of the model boundary is continuous on the model boundary. -/
private theorem continuousOn_of_eq_apply
    (hπ : ∀ z : {z : H // I z ∈ frontier (range I)}, π z = φ z) :
    ContinuousOn π {z | I z ∈ frontier (range I)} := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert φ.continuous using 1
  exact funext hπ

/-- The boundary chart attached to a chart `e` of `M`: read a boundary point through `e`, then
through the extension `π` of the homeomorphism `φ` of the model boundary. The base point `p`
witnesses that the boundary is nonempty, which `OpenPartialHomeomorph.subtypeCoord` needs to choose
an irrelevant inverse value off the target. -/
private noncomputable def boundaryChart (φ : {z : H // I z ∈ frontier (range I)} ≃ₜ F)
    (π : H → F) (hπ : ∀ z : {z : H // I z ∈ frontier (range I)}, π z = φ z) (p : I.boundary M)
    (e : OpenPartialHomeomorph M H) : OpenPartialHomeomorph (I.boundary M) F :=
  e.subtypeCoord _ ⟨p⟩ (fun y ↦ φ.symm y) π symm_symm_mem_boundary
    (symm_apply_apply_of_mem_boundary hπ) (fun y _ ↦ by rw [hπ, φ.apply_symm_apply])
    (continuous_subtypeVal.comp φ.symm.continuous)
    ((continuousOn_of_eq_apply hπ).mono fun _ ⟨_, y, hy⟩ ↦ hy ▸ (φ.symm y).property)

variable {hπ : ∀ z : {z : H // I z ∈ frontier (range I)}, π z = φ z} {p : I.boundary M}

private theorem boundaryChart_source :
    (boundaryChart φ π hπ p e).source = Subtype.val ⁻¹' e.source := by
  unfold boundaryChart
  apply OpenPartialHomeomorph.subtypeCoord_source

private theorem boundaryChart_target :
    (boundaryChart φ π hπ p e).target = {y | (φ.symm y : H) ∈ e.target} := by
  unfold boundaryChart
  apply OpenPartialHomeomorph.subtypeCoord_target

private theorem boundaryChart_apply (q : I.boundary M) :
    boundaryChart φ π hπ p e q = π (e q) := by
  unfold boundaryChart
  apply OpenPartialHomeomorph.subtypeCoord_apply

private theorem coe_boundaryChart_symm_apply {y : F} (hy : (φ.symm y : H) ∈ e.target) :
    ((boundaryChart φ π hπ p e).symm y : M) = e.symm (φ.symm y) := by
  unfold boundaryChart
  apply OpenPartialHomeomorph.coe_subtypeCoord_symm_apply
  exact hy

variable (I M) in
/-- The charted-space structure on the boundary `I.boundary M` of a charted space modelled on `H`,
with `I` a model with corners on a finite-dimensional space, induced by a homeomorphism `φ` from
the boundary of the model onto `F` and an extension `π : H → F` of `φ`. Its charts are the charts
of `M` restricted to the boundary and followed by `π`. The implementation is opaque; use the
characteristic lemmas below to reason about its charts. -/
@[irreducible] noncomputable def boundaryChartedSpaceOfHomeomorph
    (φ : {z : H // I z ∈ frontier (range I)} ≃ₜ F) (π : H → F)
    (hπ : ∀ z : {z : H // I z ∈ frontier (range I)}, π z = φ z) :
    ChartedSpace F (I.boundary M) where
  atlas := range fun p ↦ boundaryChart φ π hπ p (chartAt _ p.val)
  chartAt p := boundaryChart φ π hπ p (chartAt _ p.val)
  mem_chart_source p := by
    rw [boundaryChart_source]
    exact mem_chart_source _ p.val
  chart_mem_atlas p := mem_range_self p

/-- The preferred boundary chart at `p` is the boundary chart induced by the preferred chart of `M`
at `p`. -/
private theorem boundaryChartedSpaceOfHomeomorph_chartAt (p : I.boundary M) :
    (letI := I.boundaryChartedSpaceOfHomeomorph M φ π hπ; chartAt F p) =
      boundaryChart φ π hπ p (chartAt H (p : M)) := by
  unfold boundaryChartedSpaceOfHomeomorph
  rfl

variable (I M) in
/-- The atlas of the boundary is the range of its preferred charts. -/
theorem boundaryChartedSpaceOfHomeomorph_atlas (φ : {z : H // I z ∈ frontier (range I)} ≃ₜ F)
    (π : H → F) (hπ : ∀ z : {z : H // I z ∈ frontier (range I)}, π z = φ z) :
    (letI := I.boundaryChartedSpaceOfHomeomorph M φ π hπ; atlas F (I.boundary M)) =
      letI := I.boundaryChartedSpaceOfHomeomorph M φ π hπ
      range fun p : I.boundary M ↦ chartAt F p := by
  unfold atlas boundaryChartedSpaceOfHomeomorph chartAt
  rfl

/-- The source of the preferred boundary chart at `p` is the part of the boundary that the
preferred chart of `M` at `p` sees. -/
theorem boundaryChartedSpaceOfHomeomorph_chartAt_source (p : I.boundary M) :
    (letI := I.boundaryChartedSpaceOfHomeomorph M φ π hπ; chartAt F p).source =
      Subtype.val ⁻¹' (chartAt H (p : M)).source := by
  rw [boundaryChartedSpaceOfHomeomorph_chartAt, boundaryChart_source]

/-- The target of the preferred boundary chart at `p` is the target of the preferred chart of `M`
at `p`, pulled back along the inverse of the homeomorphism of the model boundary. -/
theorem boundaryChartedSpaceOfHomeomorph_chartAt_target (p : I.boundary M) :
    (letI := I.boundaryChartedSpaceOfHomeomorph M φ π hπ; chartAt F p).target =
      {y | (φ.symm y : H) ∈ (chartAt H (p : M)).target} := by
  rw [boundaryChartedSpaceOfHomeomorph_chartAt, boundaryChart_target]

/-- The preferred boundary chart at `p` reads a point through the preferred chart of `M` at `p`,
then through `π`. -/
theorem boundaryChartedSpaceOfHomeomorph_chartAt_apply (p q : I.boundary M) :
    (letI := I.boundaryChartedSpaceOfHomeomorph M φ π hπ; chartAt F p q) =
      π (chartAt H (p : M) q) := by
  rw [boundaryChartedSpaceOfHomeomorph_chartAt, boundaryChart_apply]

/-- On its target, the inverse of the preferred boundary chart at `p` is the inverse of the
preferred chart of `M` at `p`, applied through the inverse of the homeomorphism of the model
boundary. -/
theorem coe_boundaryChartedSpaceOfHomeomorph_chartAt_symm_apply (p : I.boundary M) {y : F}
    (hy : (φ.symm y : H) ∈ (chartAt H (p : M)).target) :
    ((letI := I.boundaryChartedSpaceOfHomeomorph M φ π hπ; chartAt F p).symm y : M) =
      (chartAt H (p : M)).symm (φ.symm y) := by
  rw [boundaryChartedSpaceOfHomeomorph_chartAt, coe_boundaryChart_symm_apply hy]

end ModelWithCorners
