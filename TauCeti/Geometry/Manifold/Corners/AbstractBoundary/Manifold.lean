/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Corners.AbstractBoundary.Basic
public import TauCeti.Geometry.Manifold.Corners.Model
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# The abstract boundary of a manifold with corners is a manifold with corners

Let `M` be a manifold modelled on the quadrant `𝓡c (m + 1)`, so that its charts take values in
`[0, ∞)^(m + 1)`. A face `{z | z i = 0}` of the quadrant is a copy of the quadrant `[0, ∞)^m` one
dimension down: deleting the vanishing coordinate `i` identifies them. This file uses that
identification to give the abstract boundary `(𝓡c (m + 1)).AbstractBoundary M` (its points are
pairs of a point of `M` and a local face through it) the structure of a manifold with corners
modelled on `𝓡c m`.

* For a chart `e` of `M` and a coordinate `i`, the face chart
  `ModelWithCorners.AbstractBoundary.faceChart` is defined on the face section of `e` along `i`,
  an open subset of the abstract boundary. It reads a point through `e` and deletes the
  coordinate `i` (`TauCeti.euclideanQuadrantFaceProj`). Its inverse reinserts a zero coordinate in
  slot `i` (`TauCeti.euclideanQuadrantFaceParam`, from
  `TauCeti.Geometry.Manifold.Corners.Model`) and applies the inverse of `e`.
* The face charts form the atlas of the abstract boundary. Their transition maps are those of
  `M`, restricted to a coordinate hyperplane and followed by the deletion of a coordinate. So the
  abstract boundary is a `C^n` manifold whenever `M` is, for every `n`, including `n = 0`.
* In the face charts the map `ModelWithCorners.AbstractBoundary.point` to `M` is the linear
  inclusion of a coordinate hyperplane, so it is `C^n`.

Two faces through a corner of `M` give two distinct points of the abstract boundary, each with its
own face chart. This is why the abstract boundary, and not the set `(𝓡c (m + 1)).boundary M`, is
the manifold one dimension down.

## Main definitions

* `ModelWithCorners.AbstractBoundary.faceChart`: the chart of the abstract boundary on a face
  section.
* `ModelWithCorners.AbstractBoundary.chartedSpace`: the instance
  `ChartedSpace (EuclideanQuadrant m) ((𝓡c (m + 1)).AbstractBoundary M)`, whose atlas consists of
  the face charts of the charts of `M` (`ModelWithCorners.AbstractBoundary.mem_atlas_iff`).

## Main results

* `ModelWithCorners.AbstractBoundary.isManifold`: the abstract boundary of a `C^n` manifold
  modelled on `𝓡c (m + 1)` is a `C^n` manifold modelled on `𝓡c m`.
* `ModelWithCorners.AbstractBoundary.contMDiff_point`: the map from the abstract boundary to `M`
  is `C^n`.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (the boundary `∂X` of a manifold with corners is
  a manifold with corners). [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.

The formal construction follows the boundary charts of a manifold modelled on the half-space in
`TauCeti.Geometry.Manifold.Boundary.Charts`: a chart of `M` is restricted to a coordinate
hyperplane and composed with the deletion of the vanishing coordinate, and the transition maps are
shown to be smooth as transition maps of `M` precomposed with the insertion of a zero coordinate
and followed by the deletion of a coordinate. Here the hyperplane may be any coordinate face of the
quadrant rather than the zeroth coordinate of the half-space. As there, the restricted chart is
`OpenPartialHomeomorph.subtypeCoord`, with the coordinate face as the slice.
-/

public section

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace ModelWithCorners.AbstractBoundary

open TauCeti

variable {m : ℕ} {M : Type*} [TopologicalSpace M]

variable {e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1))} {i : Fin (m + 1)}

/-- A point of the face `z i = 0` which the chart `e` sees lies, through `e⁻¹`, on the face of `e`
along `i`. -/
private theorem symm_faceInclusion_mem {q : EuclideanQuadrant m}
    (hq : euclideanQuadrantFaceInclusion i q ∈ e.target) :
    e.symm (euclideanQuadrantFaceInclusion i q) ∈
      {p | p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0} := by
  refine ⟨e.map_target hq, ?_⟩
  rw [OpenPartialHomeomorph.extend_coe, comp_apply, e.right_inv hq]
  simp

/-- A chart of `M` reads a point of its face along `i` on the face `z i = 0` of the quadrant. -/
private theorem faceInclusion_faceRetract {p : M}
    (hp : p ∈ {p | p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    euclideanQuadrantFaceInclusion i (euclideanQuadrantFaceRetract i (e p)) = e p :=
  euclideanQuadrantFaceInclusion_faceRetract
    (by simpa [OpenPartialHomeomorph.extend_coe] using hp.2)

/-- A chart of `M` restricted to its face along `i`, with the vanishing coordinate deleted. The
hypothesis `hs` says that the face is nonempty. -/
private def faceCoordChart (e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1)))
    (i : Fin (m + 1)) (hs : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    OpenPartialHomeomorph {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}
      (EuclideanQuadrant m) :=
  e.subtypeCoord {p | p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0} hs
    (euclideanQuadrantFaceInclusion i) (euclideanQuadrantFaceRetract i) symm_faceInclusion_mem
    (fun _ ↦ faceInclusion_faceRetract)
    (LeftInverse.leftInvOn (euclideanQuadrantFaceRetract_faceInclusion i) _)
    (continuous_euclideanQuadrantFaceInclusion i)
    (continuous_euclideanQuadrantFaceRetract i).continuousOn

/-! ### Face charts -/

variable [ChartedSpace (EuclideanQuadrant (m + 1)) M]

/-- The **face chart** of a chart `e` of `M` along the coordinate `i`: on the face section of `e`
along `i`, read the point of `M` through `e` and delete the vanishing coordinate `i`. The
hypothesis `hs` says that this face is nonempty. -/
def faceChart (he : e ∈ atlas (EuclideanQuadrant (m + 1)) M) (i : Fin (m + 1))
    (hs : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    OpenPartialHomeomorph ((𝓡c (m + 1)).AbstractBoundary M) (EuclideanQuadrant m) :=
  haveI := hs
  ((isOpenEmbedding_faceSection (he := he)
      (hi := nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i)).toOpenPartialHomeomorph
      _).symm.trans (faceCoordChart e i hs)

variable {he : e ∈ atlas (EuclideanQuadrant (m + 1)) M}
  {hs : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}}

/-- The source of a face chart is the face section. -/
@[simp]
theorem faceChart_source : (faceChart he i hs).source =
    range (faceSection he (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i)) := by
  rw [faceChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, inter_eq_left]
  -- Every point of the face section lies over the source of `e`.
  intro _ _
  rw [mem_preimage, faceCoordChart, OpenPartialHomeomorph.subtypeCoord_source, mem_preimage]
  exact (fun p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0} ↦ p.2.1) _

/-- The target of a face chart is the preimage of the target of the chart of `M` under the
inclusion of the quadrant onto the face `z i = 0`. -/
@[simp]
theorem faceChart_target :
    (faceChart he i hs).target = euclideanQuadrantFaceInclusion i ⁻¹' e.target := by
  rw [faceChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ, faceCoordChart,
    OpenPartialHomeomorph.subtypeCoord_target]

/-- A face chart reads a point of the face section through the chart of `M` and deletes the
coordinate `i`. -/
@[simp]
theorem faceChart_faceSection
    (p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    faceChart he i hs
        (faceSection he (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i) p) =
      euclideanQuadrantFaceRetract i (e p) := by
  have := hs
  simp only [faceChart, OpenPartialHomeomorph.coe_trans, comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, faceCoordChart]
  exact e.subtypeCoord_apply {p | p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0} _ _ _ _ _ _ _ _ p

/-- The inverse of a face chart reinserts a zero coordinate in slot `i` and applies the inverse
of the chart of `M`. -/
theorem point_faceChart_symm {q : EuclideanQuadrant m}
    (hq : q ∈ (faceChart he i hs).target) :
    ((faceChart he i hs).symm q).point = e.symm (euclideanQuadrantFaceInclusion i q) := by
  have := hs
  rw [faceChart_target] at hq
  simp only [faceChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.coe_trans, comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, point_faceSection, faceCoordChart]
  exact OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ _ hq

/-- A face chart, extended to the model vector space, reads a point of the face section through
the extended chart of `M` and deletes the coordinate `i`. -/
theorem extend_faceChart_faceSection
    (p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    (faceChart he i hs).extend (𝓡c m)
        (faceSection he (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i) p) =
      euclideanQuadrantFaceProj i (e.extend (𝓡c (m + 1)) p) := by
  rw [OpenPartialHomeomorph.extend_coe, comp_apply, faceChart_faceSection,
    modelWithCornersEuclideanQuadrant_euclideanQuadrantFaceRetract]
  simp only [OpenPartialHomeomorph.extend_coe, comp_apply]

/-- The target of an extended face chart is the preimage of the target of the extended chart of
`M` under the insertion of a zero coordinate in slot `i`. -/
theorem extend_faceChart_target :
    ((faceChart he i hs).extend (𝓡c m)).target =
      euclideanQuadrantFaceParam i ⁻¹' (e.extend (𝓡c (m + 1))).target := by
  ext y
  simp only [OpenPartialHomeomorph.extend_target, mem_inter_iff, mem_preimage, faceChart_target]
  constructor
  · rintro ⟨hy, q, rfl⟩
    rw [(𝓡c m).left_inv] at hy
    rw [modelWithCornersEuclideanQuadrant_apply,
      modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam]
    exact ⟨hy, (euclideanQuadrantFaceParam_mem_range_iff i).2
      ⟨q, modelWithCornersEuclideanQuadrant_apply m⟩⟩
  · rintro ⟨hy, hyr⟩
    obtain ⟨q, rfl⟩ := (euclideanQuadrantFaceParam_mem_range_iff i).1 hyr
    rw [modelWithCornersEuclideanQuadrant_apply,
      modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam] at hy
    exact ⟨by rwa [(𝓡c m).left_inv], q, rfl⟩

/-- On its target, the inverse of an extended face chart lands over the point of `M` obtained by
inserting a zero coordinate in slot `i` and applying the inverse of the extended chart of `M`. -/
theorem point_extend_faceChart_symm {y : EuclideanSpace ℝ (Fin m)}
    (hy : y ∈ ((faceChart he i hs).extend (𝓡c m)).target) :
    (((faceChart he i hs).extend (𝓡c m)).symm y).point =
      (e.extend (𝓡c (m + 1))).symm (euclideanQuadrantFaceParam i y) := by
  rw [OpenPartialHomeomorph.extend_target] at hy
  obtain ⟨hy, q, rfl⟩ := hy
  rw [mem_preimage, (𝓡c m).left_inv] at hy
  rw [OpenPartialHomeomorph.extend_coe_symm, comp_apply, (𝓡c m).left_inv,
    point_faceChart_symm hy, OpenPartialHomeomorph.extend_coe_symm, comp_apply,
    modelWithCornersEuclideanQuadrant_apply,
    modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam]

/-! ### The manifold structure -/

/-- A chart of `M` whose face section through `b.point` contains `b`. Its face chart is the
preferred chart at `b`. -/
private def baseChart (b : (𝓡c (m + 1)).AbstractBoundary M) :
    OpenPartialHomeomorph M (EuclideanQuadrant (m + 1)) :=
  (exists_faceSection_eq b).choose

private theorem baseChart_mem_atlas (b : (𝓡c (m + 1)).AbstractBoundary M) :
    baseChart b ∈ atlas (EuclideanQuadrant (m + 1)) M :=
  (exists_faceSection_eq b).choose_spec.choose

/-- The coordinate of `baseChart b` along which its face section contains `b`. -/
private def baseCoord (b : (𝓡c (m + 1)).AbstractBoundary M) : Fin (m + 1) :=
  (exists_faceSection_eq b).choose_spec.choose_spec.choose

/-- The point `b.point`, on the face of `baseChart b` along `baseCoord b`. -/
private def basePoint (b : (𝓡c (m + 1)).AbstractBoundary M) :
    {p : M // p ∈ (baseChart b).source ∧
      (baseChart b).extend (𝓡c (m + 1)) p (baseCoord b) = 0} :=
  (exists_faceSection_eq b).choose_spec.choose_spec.choose_spec.choose_spec.choose

private theorem faceSection_basePoint (b : (𝓡c (m + 1)).AbstractBoundary M) :
    faceSection (baseChart_mem_atlas b)
      (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant (baseCoord b)) (basePoint b) = b :=
  (exists_faceSection_eq b).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

/-- The abstract boundary of a manifold modelled on the quadrant `𝓡c (m + 1)` is a charted space
modelled on the quadrant `EuclideanQuadrant m`. Its atlas consists of the face charts of the
charts of `M` (`ModelWithCorners.AbstractBoundary.mem_atlas_iff`). -/
@[irreducible, instance] noncomputable def chartedSpace :
    ChartedSpace (EuclideanQuadrant m) ((𝓡c (m + 1)).AbstractBoundary M) where
  atlas := {c | ∃ (e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1)))
    (he : e ∈ atlas (EuclideanQuadrant (m + 1)) M) (i : Fin (m + 1))
    (hs : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}), c = faceChart he i hs}
  chartAt b := faceChart (baseChart_mem_atlas b) (baseCoord b) ⟨basePoint b⟩
  mem_chart_source b := by
    rw [faceChart_source]
    exact ⟨basePoint b, faceSection_basePoint b⟩
  chart_mem_atlas b := ⟨_, baseChart_mem_atlas b, _, ⟨basePoint b⟩, rfl⟩

/-- The atlas of the abstract boundary consists of the face charts of the charts of `M`. -/
theorem mem_atlas_iff
    {c : OpenPartialHomeomorph ((𝓡c (m + 1)).AbstractBoundary M) (EuclideanQuadrant m)} :
    c ∈ atlas (EuclideanQuadrant m) ((𝓡c (m + 1)).AbstractBoundary M) ↔
      ∃ (e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1)))
        (he : e ∈ atlas (EuclideanQuadrant (m + 1)) M) (i : Fin (m + 1))
        (hs : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}),
        c = faceChart he i hs := by
  unfold atlas chartedSpace
  rfl

variable {n : WithTop ℕ∞}

/-- The transition map between two face charts is `C^n`: read in the model vector spaces, it is
the transition map of `M`, precomposed with the insertion of a zero coordinate and followed by
the deletion of a coordinate. -/
private theorem contDiffOn_faceChart_symm_trans [IsManifold (𝓡c (m + 1)) n M]
    {e' : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1))}
    (he' : e' ∈ atlas (EuclideanQuadrant (m + 1)) M) {j : Fin (m + 1)}
    (hs' : Nonempty {p : M // p ∈ e'.source ∧ e'.extend (𝓡c (m + 1)) p j = 0}) :
    ContDiffOn ℝ n ((𝓡c m) ∘ ((faceChart he i hs).symm ≫ₕ faceChart he' j hs') ∘ (𝓡c m).symm)
      ((𝓡c m).symm ⁻¹' ((faceChart he i hs).symm ≫ₕ faceChart he' j hs').source ∩
        range (𝓡c m)) := by
  have hg : e.symm ≫ₕ e' ∈ contDiffGroupoid n (𝓡c (m + 1)) :=
    StructureGroupoid.compatible _ he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  -- Unpack a point of the domain: a point `q` of the target of the first face chart whose image
  -- lies on the face section of the second chart, over a point `p'` of `M`.
  have key : ∀ q : EuclideanQuadrant m,
      q ∈ ((faceChart he i hs).symm ≫ₕ faceChart he' j hs').source →
      ∃ p' : {p : M // p ∈ e'.source ∧ e'.extend (𝓡c (m + 1)) p j = 0},
        euclideanQuadrantFaceInclusion i q ∈ e.target ∧
        (p' : M) = e.symm (euclideanQuadrantFaceInclusion i q) ∧
        (faceChart he i hs).symm q =
          faceSection he' (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant j) p' := by
    intro q hq
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      faceChart_target] at hq
    obtain ⟨hq, hq'⟩ := hq
    rw [mem_preimage, faceChart_source] at hq'
    obtain ⟨p', hp'⟩ := hq'
    refine ⟨p', hq, ?_, hp'.symm⟩
    rw [← point_faceSection (he := he')
      (hi := nonneg_of_mem_range_modelWithCornersEuclideanQuadrant j) p', hp',
      point_faceChart_symm (by rwa [faceChart_target])]
  refine ContDiffOn.congr ((euclideanQuadrantFaceProj j).contDiff.comp_contDiffOn
      (hg.1.comp (euclideanQuadrantFaceParam i).contDiff.contDiffOn ?_)) ?_
  · rintro _ ⟨hy, q, rfl⟩
    rw [mem_preimage, (𝓡c m).left_inv] at hy
    obtain ⟨p', hq, hp', -⟩ := key q hy
    refine ⟨?_, (euclideanQuadrantFaceParam_mem_range_iff i).2 (mem_range_self q)⟩
    rw [mem_preimage, modelWithCornersEuclideanQuadrant_apply,
      modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨hq, by rw [mem_preimage, ← hp']; exact p'.2.1⟩
  · rintro _ ⟨hy, q, rfl⟩
    rw [mem_preimage, (𝓡c m).left_inv] at hy
    obtain ⟨p', -, hp', hq⟩ := key q hy
    simp only [comp_apply, (𝓡c m).left_inv, OpenPartialHomeomorph.coe_trans, hq,
      faceChart_faceSection, modelWithCornersEuclideanQuadrant_euclideanQuadrantFaceRetract,
      OpenPartialHomeomorph.extend_coe]
    rw [modelWithCornersEuclideanQuadrant_apply m (p := q),
      modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam, ← hp']

/-- **The abstract boundary of a `C^n` manifold with corners is a `C^n` manifold with corners**,
one dimension down: for `M` modelled on `𝓡c (m + 1)`, its abstract boundary is modelled on
`𝓡c m`. -/
instance isManifold [IsManifold (𝓡c (m + 1)) n M] :
    IsManifold (𝓡c m) n ((𝓡c (m + 1)).AbstractBoundary M) :=
  isManifold_of_contDiffOn _ _ _ fun c c' hc hc' ↦ by
    obtain ⟨e, he, i, hs, rfl⟩ := mem_atlas_iff.1 hc
    obtain ⟨e', he', j, hs', rfl⟩ := mem_atlas_iff.1 hc'
    exact contDiffOn_faceChart_symm_trans he' hs'

/-- **The map from the abstract boundary to `M` is `C^n`.** In a face chart and the chart of `M`
it comes from, it is the insertion of a zero coordinate. -/
theorem contMDiff_point [IsManifold (𝓡c (m + 1)) n M] :
    ContMDiff (𝓡c m) (𝓡c (m + 1)) n (point : (𝓡c (m + 1)).AbstractBoundary M → M) := by
  intro b
  obtain ⟨e, he, i, hs, hc⟩ := mem_atlas_iff.1 (chart_mem_atlas (EuclideanQuadrant m) b)
  have hb : b ∈ (faceChart he i hs).source := hc ▸ mem_chart_source (EuclideanQuadrant m) b
  have hbe : b.point ∈ e.source := by
    obtain ⟨p, hp⟩ := faceChart_source (hs := hs) ▸ hb
    rw [← hp, point_faceSection]
    exact p.2.1
  rw [contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (chart_mem_atlas (EuclideanQuadrant m) b))
    (IsManifold.subset_maximalAtlas he) (mem_chart_source (EuclideanQuadrant m) b) hbe, hc]
  refine ⟨continuous_point.continuousAt, ?_⟩
  -- On the target of the extended face chart, the map is the insertion of a zero coordinate.
  refine (euclideanQuadrantFaceParam i).contDiff.contDiffWithinAt.congr_of_eventuallyEq_of_mem
    ?_ (by rw [OpenPartialHomeomorph.extend_coe]; exact mem_range_self _)
  filter_upwards [(faceChart he i hs).extend_target_mem_nhdsWithin hb] with y hy
  rw [comp_apply, comp_apply, point_extend_faceChart_symm hy]
  rw [extend_faceChart_target] at hy
  exact (e.extend (𝓡c (m + 1))).right_inv hy

end ModelWithCorners.AbstractBoundary
