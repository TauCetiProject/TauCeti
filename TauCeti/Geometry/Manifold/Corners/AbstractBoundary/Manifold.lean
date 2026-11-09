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
quadrant rather than the zeroth coordinate of the half-space.
-/

public section

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace ModelWithCorners.AbstractBoundary

open TauCeti

variable {m : ℕ} {M : Type*} [TopologicalSpace M]

variable {e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1))} {i : Fin (m + 1)}

/-- A chart of `M` read on its face `i`, with the vanishing coordinate deleted. -/
private def faceCoord (e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1))) (i : Fin (m + 1))
    (p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) : EuclideanQuadrant m :=
  ⟨euclideanQuadrantFaceProj i (e p).1, fun k ↦ by simpa using (e p).2 (i.succAbove k)⟩

private theorem modelWithCornersEuclideanQuadrant_faceCoord
    (p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    (𝓡c m) (faceCoord e i p) = euclideanQuadrantFaceProj i (e.extend (𝓡c (m + 1)) p) := by
  simp [faceCoord]

private theorem faceInclusion_faceCoord
    (p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    euclideanQuadrantFaceInclusion i (faceCoord e i p) = e p := by
  apply Subtype.ext
  rw [coe_euclideanQuadrantFaceInclusion]
  exact euclideanQuadrantFaceParam_faceProj
    (by simpa [OpenPartialHomeomorph.extend_coe] using p.2.2)

private theorem continuous_faceCoord : Continuous (faceCoord e i) := by
  refine ((euclideanQuadrantFaceProj i).continuous.comp ?_).subtype_mk _
  exact continuous_subtype_val.comp
    (e.continuousOn.comp_continuous continuous_subtype_val fun p ↦ p.2.1)

/-- The range of `faceCoord` is the part of the face that the chart sees. -/
private theorem range_faceCoord :
    range (faceCoord e i) = euclideanQuadrantFaceInclusion i ⁻¹' e.target := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    rw [mem_preimage, faceInclusion_faceCoord]
    exact e.map_source p.2.1
  · intro hq
    have hp : e.symm (euclideanQuadrantFaceInclusion i q) ∈ e.source ∧
        e.extend (𝓡c (m + 1)) (e.symm (euclideanQuadrantFaceInclusion i q)) i = 0 := by
      refine ⟨e.map_target hq, ?_⟩
      rw [OpenPartialHomeomorph.extend_coe, comp_apply, e.right_inv hq]
      simp
    refine ⟨⟨_, hp⟩, Subtype.ext ?_⟩
    simp only [faceCoord]
    rw [e.right_inv hq]
    simp

private theorem isOpenEmbedding_faceCoord : IsOpenEmbedding (faceCoord e i) := by
  refine .of_continuous_injective_isOpenMap continuous_faceCoord (fun p p' h ↦ ?_) ?_
  · have h' := congrArg (euclideanQuadrantFaceInclusion i) h
    rw [faceInclusion_faceCoord, faceInclusion_faceCoord] at h'
    exact Subtype.ext (e.injOn p.2.1 p'.2.1 h')
  · intro V hV
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hV
    -- The image of the piece over `O` is cut out by the target of `e` and the preimage of `O`
    -- under its inverse.
    have hset : faceCoord e i '' (Subtype.val ⁻¹' O) =
        euclideanQuadrantFaceInclusion i ⁻¹' (e.target ∩ e.symm ⁻¹' O) := by
      ext q
      constructor
      · rintro ⟨p, hpO, rfl⟩
        rw [mem_preimage, faceInclusion_faceCoord]
        exact ⟨e.map_source p.2.1, by rwa [mem_preimage, e.left_inv p.2.1]⟩
      · rintro ⟨hq, hqO⟩
        obtain ⟨p, hp⟩ : q ∈ range (faceCoord e i) := by rwa [range_faceCoord]
        refine ⟨p, ?_, hp⟩
        rw [mem_preimage, ← e.left_inv p.2.1, ← faceInclusion_faceCoord, hp]
        exact hqO
    rw [hset]
    exact (e.isOpen_inter_preimage_symm hO).preimage
      (continuous_euclideanQuadrantFaceInclusion i)

/-! ### Face charts -/

variable [ChartedSpace (EuclideanQuadrant (m + 1)) M]

/-- The **face chart** of a chart `e` of `M` along the coordinate `i`: on the face section of `e`
along `i`, read the point of `M` through `e` and delete the vanishing coordinate `i`. The point
`p₀` of the face only witnesses that the face is nonempty; the chart does not depend on it. -/
def faceChart (he : e ∈ atlas (EuclideanQuadrant (m + 1)) M) (i : Fin (m + 1))
    (p₀ : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    OpenPartialHomeomorph ((𝓡c (m + 1)).AbstractBoundary M) (EuclideanQuadrant m) :=
  haveI : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0} := ⟨p₀⟩
  ((isOpenEmbedding_faceSection (he := he)
      (hi := nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i)).toOpenPartialHomeomorph
      _).symm.trans (isOpenEmbedding_faceCoord.toOpenPartialHomeomorph _)

variable {he : e ∈ atlas (EuclideanQuadrant (m + 1)) M}
  {p₀ : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}}

/-- The source of a face chart is the face section. -/
theorem faceChart_source : (faceChart he i p₀).source =
    range (faceSection he (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i)) := by
  rw [faceChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]

private theorem faceChart_target :
    (faceChart he i p₀).target = euclideanQuadrantFaceInclusion i ⁻¹' e.target := by
  rw [faceChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ, range_faceCoord]

private theorem faceChart_faceSection
    (p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    faceChart he i p₀
        (faceSection he (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i) p) =
      faceCoord e i p := by
  have : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0} := ⟨p₀⟩
  simp only [faceChart, OpenPartialHomeomorph.coe_trans, comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

private theorem point_faceChart_symm {q : EuclideanQuadrant m}
    (hq : q ∈ (faceChart he i p₀).target) :
    ((faceChart he i p₀).symm q).point = e.symm (euclideanQuadrantFaceInclusion i q) := by
  have : Nonempty {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0} := ⟨p₀⟩
  rw [faceChart_target, ← range_faceCoord] at hq
  set p := (isOpenEmbedding_faceCoord (e := e) (i := i)).toOpenPartialHomeomorph _ |>.symm q
  have hp : faceCoord e i p = q := IsOpenEmbedding.toOpenPartialHomeomorph_right_inv _ _ hq
  have : ((faceChart he i p₀).symm q).point = p := by
    simp only [faceChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.coe_trans, comp_apply,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply, point_faceSection, p]
  rw [this, ← hp, faceInclusion_faceCoord, e.left_inv p.2.1]

/-- A face chart, extended to the model vector space, reads a point of the face section through
the extended chart of `M` and deletes the coordinate `i`. -/
theorem extend_faceChart_faceSection
    (p : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}) :
    (faceChart he i p₀).extend (𝓡c m)
        (faceSection he (nonneg_of_mem_range_modelWithCornersEuclideanQuadrant i) p) =
      euclideanQuadrantFaceProj i (e.extend (𝓡c (m + 1)) p) := by
  rw [OpenPartialHomeomorph.extend_coe, comp_apply, faceChart_faceSection,
    modelWithCornersEuclideanQuadrant_faceCoord]

/-- The target of an extended face chart is the preimage of the target of the extended chart of
`M` under the insertion of a zero coordinate in slot `i`. -/
theorem extend_faceChart_target :
    ((faceChart he i p₀).extend (𝓡c m)).target =
      euclideanQuadrantFaceParam i ⁻¹' (e.extend (𝓡c (m + 1))).target := by
  ext y
  simp only [OpenPartialHomeomorph.extend_target, mem_inter_iff, mem_preimage, faceChart_target]
  constructor
  · rintro ⟨hy, q, rfl⟩
    rw [(𝓡c m).left_inv] at hy
    rw [modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam]
    exact ⟨hy, euclideanQuadrantFaceInclusion i q, coe_euclideanQuadrantFaceInclusion i q⟩
  · rintro ⟨hy, hyr⟩
    -- A vector whose zero extension lies in the quadrant lies in the quadrant.
    obtain ⟨q, rfl⟩ : y ∈ range (𝓡c m) := by
      rw [range_modelWithCornersEuclideanQuadrant] at hyr ⊢
      intro k
      simpa using hyr (i.succAbove k)
    rw [modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam] at hy
    exact ⟨by rwa [(𝓡c m).left_inv], q, rfl⟩

/-- On its target, the inverse of an extended face chart lands over the point of `M` obtained by
inserting a zero coordinate in slot `i` and applying the inverse of the extended chart of `M`. -/
theorem point_extend_faceChart_symm {y : EuclideanSpace ℝ (Fin m)}
    (hy : y ∈ ((faceChart he i p₀).extend (𝓡c m)).target) :
    (((faceChart he i p₀).extend (𝓡c m)).symm y).point =
      (e.extend (𝓡c (m + 1))).symm (euclideanQuadrantFaceParam i y) := by
  rw [OpenPartialHomeomorph.extend_target] at hy
  obtain ⟨hy, q, rfl⟩ := hy
  rw [mem_preimage, (𝓡c m).left_inv] at hy
  rw [OpenPartialHomeomorph.extend_coe_symm, comp_apply, (𝓡c m).left_inv,
    point_faceChart_symm hy, OpenPartialHomeomorph.extend_coe_symm, comp_apply,
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
    (p₀ : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}), c = faceChart he i p₀}
  chartAt b := faceChart (baseChart_mem_atlas b) (baseCoord b) (basePoint b)
  mem_chart_source b := by
    rw [faceChart_source]
    exact ⟨basePoint b, faceSection_basePoint b⟩
  chart_mem_atlas b := ⟨_, baseChart_mem_atlas b, _, basePoint b, rfl⟩

/-- The atlas of the abstract boundary consists of the face charts of the charts of `M`. -/
theorem mem_atlas_iff
    {c : OpenPartialHomeomorph ((𝓡c (m + 1)).AbstractBoundary M) (EuclideanQuadrant m)} :
    c ∈ atlas (EuclideanQuadrant m) ((𝓡c (m + 1)).AbstractBoundary M) ↔
      ∃ (e : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1)))
        (he : e ∈ atlas (EuclideanQuadrant (m + 1)) M) (i : Fin (m + 1))
        (p₀ : {p : M // p ∈ e.source ∧ e.extend (𝓡c (m + 1)) p i = 0}), c = faceChart he i p₀ := by
  unfold atlas chartedSpace
  rfl

variable {n : WithTop ℕ∞}

/-- The transition map between two face charts is `C^n`: read in the model vector spaces, it is
the transition map of `M`, precomposed with the insertion of a zero coordinate and followed by
the deletion of a coordinate. -/
private theorem contDiffOn_faceChart_symm_trans [IsManifold (𝓡c (m + 1)) n M]
    {e' : OpenPartialHomeomorph M (EuclideanQuadrant (m + 1))}
    (he' : e' ∈ atlas (EuclideanQuadrant (m + 1)) M) {j : Fin (m + 1)}
    (p₀' : {p : M // p ∈ e'.source ∧ e'.extend (𝓡c (m + 1)) p j = 0}) :
    ContDiffOn ℝ n ((𝓡c m) ∘ ((faceChart he i p₀).symm ≫ₕ faceChart he' j p₀') ∘ (𝓡c m).symm)
      ((𝓡c m).symm ⁻¹' ((faceChart he i p₀).symm ≫ₕ faceChart he' j p₀').source ∩
        range (𝓡c m)) := by
  have hg : e.symm ≫ₕ e' ∈ contDiffGroupoid n (𝓡c (m + 1)) :=
    StructureGroupoid.compatible _ he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  -- Unpack a point of the domain: a point `q` of the target of the first face chart whose image
  -- lies on the face section of the second chart, over a point `p'` of `M`.
  have key : ∀ q : EuclideanQuadrant m,
      q ∈ ((faceChart he i p₀).symm ≫ₕ faceChart he' j p₀').source →
      ∃ p' : {p : M // p ∈ e'.source ∧ e'.extend (𝓡c (m + 1)) p j = 0},
        euclideanQuadrantFaceInclusion i q ∈ e.target ∧
        (p' : M) = e.symm (euclideanQuadrantFaceInclusion i q) ∧
        (faceChart he i p₀).symm q =
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
    refine ⟨?_, euclideanQuadrantFaceInclusion i q, coe_euclideanQuadrantFaceInclusion i q⟩
    rw [mem_preimage, modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam]
    refine ⟨hq, ?_⟩
    simp only [mem_preimage, OpenPartialHomeomorph.symm_symm, ← hp']
    exact p'.2.1
  · rintro _ ⟨hy, q, rfl⟩
    rw [mem_preimage, (𝓡c m).left_inv] at hy
    obtain ⟨p', -, hp', hq⟩ := key q hy
    simp only [comp_apply, (𝓡c m).left_inv, OpenPartialHomeomorph.coe_trans, hq,
      faceChart_faceSection, modelWithCornersEuclideanQuadrant_symm_euclideanQuadrantFaceParam,
      modelWithCornersEuclideanQuadrant_faceCoord, OpenPartialHomeomorph.extend_coe, ← hp']

/-- **The abstract boundary of a `C^n` manifold with corners is a `C^n` manifold with corners**,
one dimension down: for `M` modelled on `𝓡c (m + 1)`, its abstract boundary is modelled on
`𝓡c m`. -/
instance isManifold [IsManifold (𝓡c (m + 1)) n M] :
    IsManifold (𝓡c m) n ((𝓡c (m + 1)).AbstractBoundary M) :=
  isManifold_of_contDiffOn _ _ _ fun c c' hc hc' ↦ by
    obtain ⟨e, he, i, p₀, rfl⟩ := mem_atlas_iff.1 hc
    obtain ⟨e', he', j, p₀', rfl⟩ := mem_atlas_iff.1 hc'
    exact contDiffOn_faceChart_symm_trans he' p₀'

/-- **The map from the abstract boundary to `M` is `C^n`.** In a face chart and the chart of `M`
it comes from, it is the insertion of a zero coordinate. -/
theorem contMDiff_point [IsManifold (𝓡c (m + 1)) n M] :
    ContMDiff (𝓡c m) (𝓡c (m + 1)) n (point : (𝓡c (m + 1)).AbstractBoundary M → M) := by
  intro b
  obtain ⟨e, he, i, p₀, hc⟩ := mem_atlas_iff.1 (chart_mem_atlas (EuclideanQuadrant m) b)
  have hb : b ∈ (faceChart he i p₀).source := hc ▸ mem_chart_source (EuclideanQuadrant m) b
  have hbe : b.point ∈ e.source := by
    obtain ⟨p, hp⟩ := faceChart_source (p₀ := p₀) ▸ hb
    rw [← hp, point_faceSection]
    exact p.2.1
  rw [contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (chart_mem_atlas (EuclideanQuadrant m) b))
    (IsManifold.subset_maximalAtlas he) (mem_chart_source (EuclideanQuadrant m) b) hbe, hc]
  refine ⟨continuous_point.continuousAt, ?_⟩
  -- On the target of the extended face chart, the map is the insertion of a zero coordinate.
  refine (euclideanQuadrantFaceParam i).contDiff.contDiffWithinAt.congr_of_eventuallyEq_of_mem
    ?_ (mem_range_self _)
  filter_upwards [(faceChart he i p₀).extend_target_mem_nhdsWithin hb] with y hy
  rw [comp_apply, comp_apply, point_extend_faceChart_symm hy]
  rw [extend_faceChart_target] at hy
  exact (e.extend (𝓡c (m + 1))).right_inv hy

end ModelWithCorners.AbstractBoundary
