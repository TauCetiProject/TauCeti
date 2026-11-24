/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Geometry.Manifold.IsManifold.InteriorChart

/-!
# The interior of a manifold with corners is a manifold without boundary

Let `M` be a charted space modelled with corners, through `I : H → E`, on a finite-dimensional
space `E`: for instance a topological manifold with boundary (the half-space model `𝓡∂ n`) or
with corners (the quadrant model `𝓡c n`). Its interior `I.interior M` is open
(`ModelWithCorners.isOpen_interior_of_finiteDimensional`), and this file makes it a charted space
modelled on the vector space `E` itself, so a manifold without boundary
(`ModelWithCorners.instChartedSpaceInterior`).

A chart `e` of `M` gives a chart `e.interiorExtend I` of the interior: the extended chart
`x ↦ I (e x)` restricted to the interior points. It is defined on all the interior points of the
source of `e` (`OpenPartialHomeomorph.interiorExtend_source`), because every chart, in the atlas or
not, reads an interior point in the interior of the range of `I`. That is the topological
invariance of the boundary, proved by invariance of domain, so no smoothness of the transition maps
is needed. Its target is the open set `I.symm ⁻¹' e.target ∩ interior (range I)` of `E`
(`OpenPartialHomeomorph.interiorExtend_target`). If `M` is a `C^n` manifold, so is its interior,
now modelled on `𝓘(𝕜, E)` (`ModelWithCorners.instIsManifoldInterior`): its transition maps are
those of `M` read on the interior of the range of `I`.

The point of the construction is that the interior of a compact topological manifold `X` with
boundary or with corners is a boundaryless manifold, open in `X` with complement the boundary
(`ModelWithCorners.range_subtypeVal_interior`). So an orientation of the interior, in the sense
of `TauCeti.HomologicalOrientation`, together with a collar of the boundary, gives the fundamental
class `[X, ∂X]` of `X` relative to its boundary
(`TauCeti.HomologicalOrientation.fundamentalClassRel`).

For a manifold `M` that is already boundaryless as a `C¹` manifold,
`TauCeti.BoundarylessModel.interiorChartedSpace` puts charts in `E` on a copy of all of `M`; here
`M` may have boundary, only its interior carries charts in `E`, and no smoothness is assumed.

## Main definitions

* `OpenPartialHomeomorph.interiorExtend`: the chart of the interior given by a chart of `M`.
* `ModelWithCorners.instChartedSpaceInterior`: the interior of `M` as a charted space modelled
  on `E`.

## Main results

* `OpenPartialHomeomorph.interiorExtend_source`, `OpenPartialHomeomorph.interiorExtend_target`,
  `OpenPartialHomeomorph.coe_interiorExtend_symm_apply`: the source, target and inverse of the
  chart of the interior given by a chart of `M`.
* `ModelWithCorners.chartAt_interior`, `ModelWithCorners.coe_chartAt_interior_symm_apply`,
  `ModelWithCorners.mem_atlas_interior_iff`: the preferred charts, their inverses and the atlas of
  the interior.
* `ModelWithCorners.instIsManifoldInterior`: the interior of a `C^n` manifold with corners is a
  `C^n` manifold modelled on `E`.
* `ModelWithCorners.contMDiff_subtypeVal_interior`: its inclusion into `M` is `C^n`.
* `ModelWithCorners.range_subtypeVal_interior`: the interior is the complement of the boundary.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1, manifolds with boundary: the interior of a manifold with boundary is an open
  submanifold without boundary.
-/

public section

noncomputable section

open Set Topology

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H M : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  [TopologicalSpace M] [ChartedSpace H M]

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph M H) [Nonempty (I.interior M)]

/-- **The chart of the interior given by a chart of `M`.** For a chart `e` of a charted space `M`
modelled with corners on a finite-dimensional space `E`, the extended chart `x ↦ I (e x)`
restricted to the interior of `M`, as an open partial homeomorphism to `E`. Its source is the set
of all interior points of the source of `e` (`OpenPartialHomeomorph.interiorExtend_source`), and
its target is the open set `I.symm ⁻¹' e.target ∩ interior (range I)`
(`OpenPartialHomeomorph.interiorExtend_target`). -/
def interiorExtend : OpenPartialHomeomorph (I.interior M) E :=
  ((I.isOpen_interior_of_finiteDimensional M).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    Subtype.val).trans (e.trans I.interiorChart)

/-- The chart of the interior given by `e` is the extended chart of `e`. -/
@[simp, mfld_simps]
theorem interiorExtend_apply (x : I.interior M) : e.interiorExtend I x = I (e x) := by
  simp only [interiorExtend, coe_trans, Function.comp_apply, ModelWithCorners.interiorChart_coe,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply]

/-- The chart of the interior given by `e` is defined at every interior point of the source of
`e`: every chart reads an interior point in the interior of the range of `I`. -/
@[simp, mfld_simps]
theorem interiorExtend_source : (e.interiorExtend I).source = Subtype.val ⁻¹' e.source := by
  ext x
  simp only [interiorExtend, trans_source, IsOpenEmbedding.toOpenPartialHomeomorph_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, ModelWithCorners.interiorChart_source,
    mem_inter_iff, mem_univ, mem_preimage, true_and, and_iff_left_iff_imp]
  exact fun hx ↦ (I.isInteriorPoint_iff_mem_interior_range_of_finiteDimensional hx).1 x.property

/-- The target of the chart of the interior given by `e` is the set of points of the interior of
the range of `I` whose coordinates lie in the target of `e`. -/
@[simp, mfld_simps]
theorem interiorExtend_target :
    (e.interiorExtend I).target = I.symm ⁻¹' e.target ∩ interior (range I) := by
  ext v
  simp only [interiorExtend, trans_target, IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Subtype.range_coe_subtype, ModelWithCorners.interiorChart_target,
    ModelWithCorners.interiorChart_coe_symm, trans_symm_eq_symm_trans_symm, coe_trans,
    Function.comp_apply, mem_inter_iff, mem_preimage]
  refine ⟨fun ⟨⟨hv, he⟩, _⟩ ↦ ⟨he, hv⟩, fun ⟨he, hv⟩ ↦ ⟨⟨hv, he⟩, ?_⟩⟩
  -- The point `e.symm (I.symm v)` of the source of `e` is read by `e` at `v`, an interior point
  -- of the range of `I`, so it is an interior point of `M`.
  refine (I.isInteriorPoint_iff_mem_interior_range_of_finiteDimensional (e.map_target he)).2 ?_
  rwa [e.right_inv he, I.right_inv (interior_subset hv)]

/-- The inverse of the chart of the interior given by `e` is the inverse of the extended chart of
`e`. -/
theorem coe_interiorExtend_symm_apply {v : E} (hv : v ∈ (e.interiorExtend I).target) :
    ((e.interiorExtend I).symm v : M) = e.symm (I.symm v) := by
  have h := (e.interiorExtend I).right_inv hv
  rw [interiorExtend_apply] at h
  have hsrc : ((e.interiorExtend I).symm v : M) ∈ e.source := by
    have := (e.interiorExtend I).map_target hv
    rwa [interiorExtend_source] at this
  rw [← e.left_inv hsrc, ← I.left_inv (e _), h]

end OpenPartialHomeomorph

namespace ModelWithCorners

/-- **The interior of a manifold with corners is a manifold without boundary.** The interior of a
charted space modelled with corners on a finite-dimensional space `E` is a charted space modelled
on `E`: its charts are the restrictions of the extended charts of `M` to the interior points
(`OpenPartialHomeomorph.interiorExtend`). -/
instance instChartedSpaceInterior : ChartedSpace E (I.interior M) where
  atlas := {f | ∃ (_ : Nonempty (I.interior M)) (e : OpenPartialHomeomorph M H),
    e ∈ atlas H M ∧ f = e.interiorExtend I}
  chartAt x :=
    have : Nonempty (I.interior M) := ⟨x⟩
    (chartAt H (x : M)).interiorExtend I
  mem_chart_source x := by
    have : Nonempty (I.interior M) := ⟨x⟩
    simp only [OpenPartialHomeomorph.interiorExtend_source, mem_preimage, mem_chart_source]
  chart_mem_atlas x := ⟨⟨x⟩, _, chart_mem_atlas H _, rfl⟩

/-- The preferred chart of the interior at `x` is the chart of the interior given by the preferred
chart of `M` at `x`. -/
theorem chartAt_interior (x : I.interior M) :
    have : Nonempty (I.interior M) := ⟨x⟩
    chartAt E x = (chartAt H (x : M)).interiorExtend I :=
  (rfl)

/-- The preferred chart of the interior at `x` is the extended preferred chart of `M` at `x`. -/
@[simp, mfld_simps]
theorem chartAt_interior_apply (x y : I.interior M) :
    chartAt E x y = I (chartAt H (x : M) y) := by
  have : Nonempty (I.interior M) := ⟨x⟩
  exact (chartAt H (x : M)).interiorExtend_apply I y

/-- The preferred chart of the interior at `x` is defined at every interior point of the source
of the preferred chart of `M` at `x`. -/
@[simp, mfld_simps]
theorem chartAt_interior_source (x : I.interior M) :
    (chartAt E x).source = Subtype.val ⁻¹' (chartAt H (x : M)).source := by
  have : Nonempty (I.interior M) := ⟨x⟩
  rw [chartAt_interior, OpenPartialHomeomorph.interiorExtend_source]

/-- The target of the preferred chart of the interior at `x`. -/
@[simp, mfld_simps]
theorem chartAt_interior_target (x : I.interior M) :
    (chartAt E x).target = I.symm ⁻¹' (chartAt H (x : M)).target ∩ interior (range I) := by
  have : Nonempty (I.interior M) := ⟨x⟩
  rw [chartAt_interior, OpenPartialHomeomorph.interiorExtend_target]

/-- The inverse of the preferred chart of the interior at `x` is the inverse of the extended
preferred chart of `M` at `x`. -/
theorem coe_chartAt_interior_symm_apply (x : I.interior M) {v : E}
    (hv : v ∈ (chartAt E x).target) :
    ((chartAt E x).symm v : M) = (chartAt H (x : M)).symm (I.symm v) := by
  have : Nonempty (I.interior M) := ⟨x⟩
  exact (chartAt H (x : M)).coe_interiorExtend_symm_apply I hv

/-- The charts of the atlas of the interior are the charts of the interior given by the charts of
the atlas of `M`. -/
theorem mem_atlas_interior_iff [Nonempty (I.interior M)]
    {f : OpenPartialHomeomorph (I.interior M) E} :
    f ∈ atlas E (I.interior M) ↔ ∃ e ∈ atlas H M, f = e.interiorExtend I :=
  ⟨fun ⟨_, e, he, hf⟩ ↦ ⟨e, he, hf⟩, fun ⟨e, he, hf⟩ ↦ ⟨inferInstance, e, he, hf⟩⟩

/-- **The interior of a `C^n` manifold with corners is a `C^n` manifold**, modelled on the vector
space `E` with its trivial model with corners. A transition map of the interior is a transition
map of `M` read on the interior of the range of `I`. -/
instance instIsManifoldInterior {n : WithTop ℕ∞} [IsManifold I n M] :
    IsManifold 𝓘(𝕜, E) n (I.interior M) := by
  refine isManifold_of_contDiffOn _ _ _ fun f f' hf hf' ↦ ?_
  obtain ⟨_, e, he, rfl⟩ := hf
  obtain ⟨_, e', he', rfl⟩ := hf'
  -- The transition map `e.symm ≫ₕ e'` of `M` is `C^n` in the coordinates of `I`.
  have hG := (mem_groupoid_of_pregroupoid.1
    (StructureGroupoid.compatible (contDiffGroupoid n I) he he')).1
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
    Function.id_comp, Function.comp_id, preimage_id, inter_univ]
  have hsrc {v : E} (hv : v ∈ ((e.interiorExtend I).symm ≫ₕ e'.interiorExtend I).source) :
      I.symm v ∈ e.target ∧ v ∈ interior (range I) ∧ e.symm (I.symm v) ∈ e'.source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.interiorExtend_target, OpenPartialHomeomorph.interiorExtend_source,
      mem_inter_iff, mem_preimage] at hv
    rw [OpenPartialHomeomorph.coe_interiorExtend_symm_apply I e (by simpa using hv.1)] at hv
    exact ⟨hv.1.1, hv.1.2, hv.2⟩
  refine (hG.mono fun v hv ↦ ?_).congr fun v hv ↦ ?_
  · obtain ⟨h₁, h₂, h₃⟩ := hsrc hv
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨⟨h₁, h₃⟩, interior_subset h₂⟩
  · obtain ⟨h₁, h₂, -⟩ := hsrc hv
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.interiorExtend_apply]
    rw [OpenPartialHomeomorph.coe_interiorExtend_symm_apply I e (by simpa using And.intro h₁ h₂)]

/-- **The inclusion of the interior is smooth.** For every `n`, the inclusion of the interior of
`M`, with its charts in `E`, into `M` is `C^n`: read in the preferred charts it is the identity
of `E` near each point. No smoothness of `M` is needed. -/
theorem contMDiff_subtypeVal_interior {n : WithTop ℕ∞} :
    ContMDiff 𝓘(𝕜, E) I n (Subtype.val : I.interior M → M) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtypeVal.continuousAt, ?_⟩
  simp only [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  have hx : extChartAt 𝓘(𝕜, E) x x ∈ (chartAt E x).target := by
    simpa using (chartAt E x).map_source (mem_chart_source E x)
  refine contDiffAt_id.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with v hv
  -- On the target of the chart of the interior, its inverse is the inverse of the extended chart
  -- of `M` at `x`, which the extended chart of `M` at `x` undoes.
  have hv' := hv
  rw [chartAt_interior_target] at hv'
  simp only [Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, id_eq]
  rw [coe_chartAt_interior_symm_apply I x hv, (chartAt H (x : M)).right_inv hv'.1,
    I.right_inv (interior_subset hv'.2)]

omit [FiniteDimensional 𝕜 E] in
/-- The interior of `M` is the complement of its boundary. -/
theorem range_subtypeVal_interior :
    range (Subtype.val : I.interior M → M) = (range (Subtype.val : I.boundary M → M))ᶜ := by
  rw [Subtype.range_coe, Subtype.range_coe, compl_boundary]

end ModelWithCorners
