/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Boundary.Basic
public import TauCeti.Geometry.Manifold.Boundary.Invariance
public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Geometry.Manifold.Boundary.OfHomeomorph
import TauCeti.Topology.Homeomorph.Prod

/-!
# The boundary of a manifold with boundary is a manifold

Mathlib carries the boundary `I.boundary M` of a manifold with boundary only as a *set*: there is
no manifold structure on it, so nothing can be glued along it. This file supplies that structure in
the basic Euclidean half-space case. For any charted space `M` modeled on the `(n + 1)`-dimensional
Euclidean half-space `𝓡∂ (n + 1)` the boundary carries a charted-space structure modeled on
`EuclideanSpace ℝ (Fin n)`, one dimension lower. When `M` is a `C^k` manifold, its boundary is a
boundaryless `C^k` manifold whose inclusion into `M` is a `C^k` smooth embedding.

The boundary atlas consists of charts induced by the preferred ambient charts. Each preferred
ambient chart carries a boundary point to a point of the half-space whose zeroth coordinate
vanishes; deleting that coordinate turns it into a preferred chart of the boundary. Two facts make
this work, and they are the content of the file.

* **The boundary is visible in every chart.** Mathlib defines a boundary point through the chart
  *at that point*. Detecting it in any other chart is the topological invariance of the boundary,
  `ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional`, which rests on
  invariance of domain and needs no smoothness. This file specialises it to the Euclidean
  half-space equation `x ∈ ∂M ↔ (e x) 0 = 0`.
* **The transition maps stay `C^k`.** A boundary transition map is the ambient transition map
  conjugated by the linear parametrization of the coordinate hyperplane, and `ContDiffOn` composes
  with continuous linear maps, so no new analysis is needed.

The charted-space structure is the general construction
`ModelWithCorners.boundaryChartedSpaceOfHomeomorph` for the deletion of the zeroth coordinate. It
depends only on the ambient charts and is registered as the canonical instance, so the same
structure serves smooth, PL and topological manifolds with boundary. The manifold and embedding
results hold for every exponent `k`. Boundarylessness then follows directly from
`ModelWithCorners.Boundaryless.boundary_eq_empty`.

Corners are deliberately out of scope: gluing along a *piece* of the boundary produces corners, and
the quadrant model `modelWithCornersEuclideanQuadrant` needs its own boundary analysis. Only its
chart test for boundary points, the analogue of the half-space one, is recorded here. Collar
neighbourhoods, which are what make a gluing smooth rather than merely topological, are the next
step and are not proved here.

## Main definitions

* `TauCeti.boundaryChartedSpace`: the charted-space structure on `I.boundary M`.

## Main results

* `TauCeti.ModelWithCorners.mem_boundary_euclideanHalfSpace_iff`: boundary points are detected by
  the vanishing zeroth coordinate in any ambient chart.
* `TauCeti.ModelWithCorners.isInteriorPoint_euclideanHalfSpace_iff`: interior points are detected
  by the positive zeroth coordinate in any ambient chart.
* `TauCeti.mem_boundary_iff_transHomeomorph_prodUnique`: the same boundary criterion in an ambient
  chart read with a trivial second factor, the form taken by the hyperplane and product charts.
* `TauCeti.boundaryChartedSpace_atlas`: the boundary atlas is the range of its preferred charts.
* `TauCeti.boundaryChartedSpace_chartAt_source` and its companions characterize the preferred
  boundary charts induced by the ambient preferred charts.
* `TauCeti.eqOn_boundaryChartedSpace_chartAt_symm_trans` and
  `TauCeti.mapsTo_boundaryParam_boundaryChartedSpace_chartAt_symm_trans`: a boundary transition map
  is the ambient transition map conjugated by the linear parametrization of the coordinate
  hyperplane and the linear deletion of the zeroth coordinate.
* `TauCeti.isManifold_boundary`: the boundary is a `C^k` manifold over `EuclideanSpace ℝ (Fin n)`.
* `TauCeti.isImmersion_subtypeVal_boundary`, `TauCeti.isSmoothEmbedding_subtypeVal_boundary`: the
  inclusion of the boundary is a `C^k` smooth embedding.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1 (manifolds with boundary).
* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 1.46 (the
  boundary of a smooth `n`-manifold with boundary is a smooth `(n - 1)`-manifold).
-/

public section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

section Interior

variable {d : ℕ} [NeZero d] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace d) M]

/-- A point of a charted space modeled on the `d`-dimensional Euclidean half-space is an interior
point exactly when any chart around it reads it with positive zeroth coordinate. -/
theorem ModelWithCorners.isInteriorPoint_euclideanHalfSpace_iff
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace d)} {x : M} (hx : x ∈ e.source) :
    (𝓡∂ d).IsInteriorPoint x ↔ 0 < (e x).val 0 := by
  rw [ModelWithCorners.isInteriorPoint_iff_mem_interior_range_of_finiteDimensional hx,
    interior_range_modelWithCornersEuclideanHalfSpace, modelWithCornersEuclideanHalfSpace_toFun]
  exact Iff.rfl

end Interior

section Boundary

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))} {x : M}

/-- A point of a charted space modeled on the `(n + 1)`-dimensional Euclidean half-space lies on
the boundary exactly when any chart around it reads it with vanishing zeroth coordinate. -/
theorem ModelWithCorners.mem_boundary_euclideanHalfSpace_iff (hx : x ∈ e.source) :
    x ∈ (𝓡∂ (n + 1)).boundary M ↔ (e x).val 0 = 0 :=
  (ModelWithCorners.mem_boundary_iff_mem_frontier_range_of_finiteDimensional hx).trans
    (modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff _)

variable (n) in
/-- Deleting the zeroth coordinate identifies the points that the half-space model sends to the
frontier of its range with `EuclideanSpace ℝ (Fin n)`. -/
private noncomputable def euclideanHalfSpaceFrontierHomeomorph :
    {z : EuclideanHalfSpace (n + 1) // (𝓡∂ (n + 1)) z ∈ frontier (range (𝓡∂ (n + 1)))} ≃ₜ
      EuclideanSpace ℝ (Fin n) where
  toFun z := EuclideanHalfSpace.boundaryProj n z.val
  invFun y := ⟨EuclideanHalfSpace.boundaryParam n y,
    (modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff _).2 (by simp)⟩
  left_inv z := Subtype.ext <| by
    dsimp only
    rw [EuclideanHalfSpace.boundaryProj_coe]
    exact EuclideanHalfSpace.boundaryParam_boundaryProj
      ((modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff _).1 z.property)
  right_inv := EuclideanHalfSpace.boundaryProj_boundaryParam
  continuous_toFun := EuclideanHalfSpace.continuous_boundaryProj.comp continuous_subtypeVal
  continuous_invFun := EuclideanHalfSpace.continuous_boundaryParam.subtype_mk _

private theorem euclideanHalfSpaceFrontierHomeomorph_apply
    (z : {z : EuclideanHalfSpace (n + 1) // (𝓡∂ (n + 1)) z ∈ frontier (range (𝓡∂ (n + 1)))}) :
    euclideanHalfSpaceFrontierHomeomorph n z = EuclideanHalfSpace.boundaryProj n z.val :=
  (rfl)

private theorem coe_euclideanHalfSpaceFrontierHomeomorph_symm_apply
    (z : EuclideanSpace ℝ (Fin n)) :
    ((euclideanHalfSpaceFrontierHomeomorph n).symm z : EuclideanHalfSpace (n + 1)) =
      EuclideanHalfSpace.boundaryParam n z :=
  (rfl)

variable (e) in
/-- In any ambient chart, read with a trivial second factor, the boundary is the hyperplane where
the zeroth coordinate vanishes. -/
theorem mem_boundary_iff_transHomeomorph_prodUnique {F : Type*} [TopologicalSpace F] [Unique F] :
    ∀ w ∈ (e.transHomeomorph (Homeomorph.prodUnique _ F).symm).source,
      w ∈ (𝓡∂ (n + 1)).boundary M ↔
        (e.transHomeomorph (Homeomorph.prodUnique _ F).symm w).1.val 0 = 0 :=
  fun _ hw ↦ by
    simpa using ModelWithCorners.mem_boundary_euclideanHalfSpace_iff (by simpa using hw)

section BoundaryChartedSpace

/-- The canonical charted-space structure on the boundary of a charted space modeled on a
Euclidean half-space. Its charts are the ambient charts restricted to the boundary, with the
vanishing zeroth coordinate deleted: the general construction
`ModelWithCorners.boundaryChartedSpaceOfHomeomorph` for the deletion of that coordinate. The
implementation is intentionally opaque; use the characteristic lemmas below to reason about its
atlas and preferred charts. -/
@[irreducible, instance] noncomputable def boundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) :=
  (𝓡∂ (n + 1)).boundaryChartedSpaceOfHomeomorph M (euclideanHalfSpaceFrontierHomeomorph n)
    (EuclideanHalfSpace.boundaryProj n) fun z ↦
      (euclideanHalfSpaceFrontierHomeomorph_apply z).symm

variable (M) in
/-- The boundary atlas is the range of its preferred charts. -/
theorem boundaryChartedSpace_atlas :
    atlas (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) =
      range fun p : ↥((𝓡∂ (n + 1)).boundary M) ↦
        chartAt (EuclideanSpace ℝ (Fin n)) p :=
  by
    unfold boundaryChartedSpace
    exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_atlas _ _ _ _ _

variable (M) in
/-- The source of the preferred boundary chart at `p` is the part of the boundary the ambient
preferred chart at `p` sees. -/
theorem boundaryChartedSpace_chartAt_source (p : ↥((𝓡∂ (n + 1)).boundary M)) :
    (chartAt (EuclideanSpace ℝ (Fin n)) p).source =
      Subtype.val ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).source :=
  by
    unfold boundaryChartedSpace
    exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_source p

variable (M) in
/-- The target of the preferred boundary chart at `p` is the ambient target, pulled back to the
coordinate hyperplane. -/
theorem boundaryChartedSpace_chartAt_target (p : ↥((𝓡∂ (n + 1)).boundary M)) :
    (chartAt (EuclideanSpace ℝ (Fin n)) p).target =
      EuclideanHalfSpace.boundaryParam n ⁻¹'
        (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target :=
  by
    unfold boundaryChartedSpace
    ext z
    rw [ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_target, mem_ofPred_eq,
      coe_euclideanHalfSpaceFrontierHomeomorph_symm_apply, mem_preimage]

variable (M) in
/-- The preferred boundary chart at `p` reads a point through the ambient preferred chart at `p`
and deletes the zeroth coordinate. -/
theorem boundaryChartedSpace_chartAt_apply (p q : ↥((𝓡∂ (n + 1)).boundary M)) :
    chartAt (EuclideanSpace ℝ (Fin n)) p q =
      EuclideanHalfSpace.boundaryProj n
        (chartAt (EuclideanHalfSpace (n + 1)) (p : M) (q : M)) :=
  by
    unfold boundaryChartedSpace
    exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_apply p q

variable (M) in
/-- On its target, the inverse of the preferred boundary chart at `p` is the inverse of the ambient
preferred chart at `p`, applied to the parametrized point. -/
theorem boundaryChartedSpace_chartAt_symm_apply (p : ↥((𝓡∂ (n + 1)).boundary M))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : EuclideanHalfSpace.boundaryParam n z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target) :
    (((chartAt (EuclideanSpace ℝ (Fin n)) p).symm z : ↥((𝓡∂ (n + 1)).boundary M)) : M) =
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm
        (EuclideanHalfSpace.boundaryParam n z) :=
  by
    unfold boundaryChartedSpace
    rw [← coe_euclideanHalfSpaceFrontierHomeomorph_symm_apply] at hz ⊢
    exact ModelWithCorners.coe_boundaryChartedSpaceOfHomeomorph_chartAt_symm_apply p hz

end BoundaryChartedSpace

section Transition

variable (p q : ↥((𝓡∂ (n + 1)).boundary M))

variable (M) in
/-- The parametrization of the coordinate hyperplane carries the source of the transition map
between the preferred boundary charts at `p` and `q` into the domain of the ambient transition map
between the preferred charts at `p` and `q`, read in the model vector space. -/
theorem mapsTo_boundaryParam_boundaryChartedSpace_chartAt_symm_trans :
    MapsTo (euclideanHalfSpaceBoundaryParam n)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ≫ₕ
        chartAt (EuclideanSpace ℝ (Fin n)) q).source
      ((𝓡∂ (n + 1)).symm ⁻¹' ((chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm ≫ₕ
        chartAt (EuclideanHalfSpace (n + 1)) (q : M)).source ∩ range (𝓡∂ (n + 1))) := by
  intro z hz
  have h₁ : EuclideanHalfSpace.boundaryParam n z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target := by
    have h := hz.1
    rwa [OpenPartialHomeomorph.symm_symm, boundaryChartedSpace_chartAt_target M p] at h
  have h₂ := hz.2
  rw [OpenPartialHomeomorph.symm_symm, mem_preimage, boundaryChartedSpace_chartAt_source M q,
    mem_preimage, boundaryChartedSpace_chartAt_symm_apply M p h₁] at h₂
  refine ⟨?_, EuclideanHalfSpace.boundaryParam_mem_range z⟩
  rw [mem_preimage, EuclideanHalfSpace.modelWithCornersEuclideanHalfSpace_symm_boundaryParam]
  exact ⟨h₁, h₂⟩

variable (M) in
/-- On its source, the transition map between the preferred boundary charts at `p` and `q` is the
ambient transition map between the preferred charts at `p` and `q`, read in the model vector space
and conjugated by the linear parametrization of the coordinate hyperplane and the linear deletion
of the zeroth coordinate. Any regularity class stable under composition with linear maps therefore
passes from the ambient transition maps to the boundary ones. -/
theorem eqOn_boundaryChartedSpace_chartAt_symm_trans :
    EqOn ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ≫ₕ chartAt (EuclideanSpace ℝ (Fin n)) q)
      (euclideanHalfSpaceBoundaryProj n ∘
        ((𝓡∂ (n + 1)) ∘ ((chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm ≫ₕ
          chartAt (EuclideanHalfSpace (n + 1)) (q : M)) ∘ (𝓡∂ (n + 1)).symm) ∘
        euclideanHalfSpaceBoundaryParam n)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ≫ₕ
        chartAt (EuclideanSpace ℝ (Fin n)) q).source := by
  intro z hz
  have h₁ : EuclideanHalfSpace.boundaryParam n z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target := by
    have h := hz.1
    rwa [OpenPartialHomeomorph.symm_symm, boundaryChartedSpace_chartAt_target M p] at h
  simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans,
    boundaryChartedSpace_chartAt_apply,
    EuclideanHalfSpace.modelWithCornersEuclideanHalfSpace_symm_boundaryParam,
    EuclideanHalfSpace.boundaryProj_coe]
  rw [boundaryChartedSpace_chartAt_symm_apply M p h₁, modelWithCornersEuclideanHalfSpace_toFun]

end Transition

variable [IsManifold (𝓡∂ (n + 1)) k M]

/-- The transition map between two preferred boundary charts is `C^k`: read through the
parametrization of the coordinate hyperplane it is the ambient transition map, restricted to that
hyperplane. -/
private theorem contDiffOn_boundaryChartedSpace_chartAt_symm_trans
    (p q : ↥((𝓡∂ (n + 1)).boundary M)) :
    ContDiffOn ℝ k
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ≫ₕ chartAt (EuclideanSpace ℝ (Fin n)) q)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm ≫ₕ
        chartAt (EuclideanSpace ℝ (Fin n)) q).source := by
  have hg : (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm ≫ₕ
      chartAt (EuclideanHalfSpace (n + 1)) (q : M) ∈ contDiffGroupoid k (𝓡∂ (n + 1)) :=
    StructureGroupoid.compatible _ (chart_mem_atlas _ (p : M)) (chart_mem_atlas _ (q : M))
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  exact ((euclideanHalfSpaceBoundaryProj n).contDiff.comp_contDiffOn
    (hg.1.comp (euclideanHalfSpaceBoundaryParam n).contDiff.contDiffOn
      (mapsTo_boundaryParam_boundaryChartedSpace_chartAt_symm_trans M p q))).congr
    (eqOn_boundaryChartedSpace_chartAt_symm_trans M p q)

variable (M) in
/-- **The boundary of a `C^k` manifold with boundary is a `C^k` manifold** of dimension one less:
the transition maps between the boundary charts are `C^k`. -/
theorem isManifold_boundary :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k ↥((𝓡∂ (n + 1)).boundary M) := by
  refine isManifold_of_contDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
    ↥((𝓡∂ (n + 1)).boundary M) ?_
  rw [boundaryChartedSpace_atlas]
  rintro f₁ f₂ ⟨p, rfl⟩ ⟨q, rfl⟩
  simpa using contDiffOn_boundaryChartedSpace_chartAt_symm_trans p q

variable (M) in
/-- The inclusion of the boundary into the manifold is a `C^k` immersion. In the preferred
boundary and ambient charts it is the coordinate inclusion with one-dimensional complement. -/
theorem isImmersion_subtypeVal_boundary :
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) k
      (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) := by
  let _ := isManifold_boundary (n := n) (k := k) M
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ℝ)
  intro p
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtypeVal.continuousAt (euclideanHalfSpaceBoundaryNormalEquiv n)
    (chartAt (EuclideanSpace ℝ (Fin n)) p)
    (chartAt (EuclideanHalfSpace (n + 1)) (p : M))
    (mem_chart_source _ p) (mem_chart_source _ (p : M))
    (IsManifold.chart_mem_maximalAtlas p) (IsManifold.chart_mem_maximalAtlas (p : M))
  intro z hz
  rw [OpenPartialHomeomorph.extend_target] at hz
  have hzdom : z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
    simpa only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq] using hz.1
  have hz' : EuclideanHalfSpace.boundaryParam n z ∈
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).target := by
    rw [boundaryChartedSpace_chartAt_target M p] at hzdom
    exact hzdom
  have h1 : ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm z : M) =
      (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).symm
        (EuclideanHalfSpace.boundaryParam n z) :=
    boundaryChartedSpace_chartAt_symm_apply M p hz'
  simp only [Function.comp_apply, mfld_simps]
  rw [h1, (chartAt (EuclideanHalfSpace (n + 1)) (p : M)).right_inv hz',
    modelWithCornersEuclideanHalfSpace_toFun, EuclideanHalfSpace.boundaryParam_coe]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

variable (M) in
/-- The inclusion of the boundary into the manifold is a `C^k` smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_boundary :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) k
      (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) :=
  ⟨isImmersion_subtypeVal_boundary (n := n) (k := k) M, IsEmbedding.subtypeVal⟩

end Boundary

end TauCeti
