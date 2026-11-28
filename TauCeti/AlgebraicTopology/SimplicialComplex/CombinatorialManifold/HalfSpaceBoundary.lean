/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ChartedSpace
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.Boundary
public import TauCeti.Geometry.Manifold.Boundary.Homeomorph
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction

/-!
# Manifold boundary of the realization of a combinatorial manifold

The charted-space structure `IsCombinatorialManifold.realizationChartedSpace` on the weak
realization of a positive-dimensional combinatorial manifold is only a topological manifold with
boundary, so its manifold boundary cannot be determined by taking derivatives. By topological
invariance of the boundary
(`ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional` and
`Homeomorph.isBoundaryPoint_iff`), every half-space chart detects boundary points cleanly.

Proceeding by induction on the dimension `n`, we prove that for any combinatorial
`(n + 1)`-manifold `K`, a point `x : Realization K` is a manifold boundary point if and only if
its carrier `x.val.support` belongs to `K.toPreAbstractSimplicialComplex.manifoldBoundary`.
In particular, the manifold boundary of `Realization K` is
`{x | x.val.support ∈ manifoldBoundary K}`.

## Main results

* `PreAbstractSimplicialComplex.IsCombinatorialManifold.`
  `isBoundaryPoint_realizationChartedSpace_iff`:
  characterization of boundary points of `Realization K` via `manifoldBoundary`.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.boundary_realizationChartedSpace`:
  `(𝓡∂ (n + 1)).boundary (Realization K) = {x | x.val.support ∈ manifoldBoundary K}`.
* `PreAbstractSimplicialComplex.IsCombinatorialManifold.interior_realizationChartedSpace`:
  `(𝓡∂ (n + 1)).interior (Realization K) = {x | x.val.support ∉ manifoldBoundary K}`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2–3 (boundary of a combinatorial manifold).
-/

public section

noncomputable section

open AbstractSimplicialComplex Metric Set Topology TauCeti
open scoped Manifold RealInnerProductSpace

namespace PreAbstractSimplicialComplex

universe u

variable {ι : Type u} [DecidableEq ι]

private theorem link_restrictToVerticesRealizationHomeomorph_support_mem_manifoldBoundary_iff
    {K : AbstractSimplicialComplex ι} (v : ι)
    (z : Realization (link K.toPreAbstractSimplicialComplex {v}).restrictToVertices) :
    (restrictToVerticesRealizationHomeomorph (K := K)
        (link_le (K := K.toPreAbstractSimplicialComplex) (σ := {v})) z).val.val.support ∈
        manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) ↔
      z.val.support ∈ manifoldBoundary
        (link K.toPreAbstractSimplicialComplex
          {v}).restrictToVertices.toPreAbstractSimplicialComplex := by
  rw [restrictToVerticesRealizationHomeomorph_val,
    Finsupp.mapDomain_support_of_injective Subtype.val_injective]
  have hmb : manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) =
      (manifoldBoundary
        (link K.toPreAbstractSimplicialComplex
          {v}).restrictToVertices.toPreAbstractSimplicialComplex).map
        (Function.Embedding.subtype _) := by
    conv_lhs => rw [← map_val_restrictToVertices (link K.toPreAbstractSimplicialComplex {v})]
    exact (map_manifoldBoundary _ Subtype.val_injective).symm
  rw [hmb, mem_map_iff]
  constructor
  · rintro ⟨σ, hσ, heq⟩
    have hinj : Function.Injective (Finset.image (Subtype.val :
        {w : ι // ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v}} → ι)) :=
      Finset.image_injective Subtype.val_injective
    rwa [← hinj heq]
  · intro hz
    exact ⟨z.val.support, hz, rfl⟩

private theorem mem_manifoldBoundary_of_openStar_lt_one {K : AbstractSimplicialComplex ι}
    {n : ℕ} (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex n) {v : ι}
    {x : Realization K} (hx : x ∈ K.openStarRealization v) (hlt : x.val v < 1) :
    x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex ↔
      (starLinkProjection K v ⟨x, (K.mem_puncturedClosedStar v x).mpr
        ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩).val.val.support ∈
          manifoldBoundary (link K.toPreAbstractSimplicialComplex {v}) := by
  let p₀ : puncturedClosedStar K v := ⟨x, (K.mem_puncturedClosedStar v x).mpr
    ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩
  rw [support_starLinkProjection K v p₀, ← h.link_manifoldBoundary {v}, mem_link_nonempty]
  have hvsup : v ∈ x.val.support := (K.mem_openStarRealization_iff_mem_support).mp hx
  have hne : (x.val.support.erase v).Nonempty := by
    rw [← support_starLinkProjection K v p₀, Finsupp.support_nonempty_iff]
    intro h0
    have hsum := Realization.sum_eq_one K (starLinkProjection K v p₀).val
    simp [h0] at hsum
  have hdisj : Disjoint (x.val.support.erase v) {v} :=
    Finset.disjoint_singleton_right.mpr (Finset.notMem_erase v _)
  have hunion : x.val.support.erase v ∪ {v} = x.val.support := by
    rw [Finset.union_singleton, Finset.insert_erase hvsup]
  rw [hunion]
  exact ⟨fun hxbd => ⟨hne, hdisj, hxbd⟩, fun h3 => h3.2.2⟩

/-- Identification of the open half-ball `ball 0 1 ∩ {z | 0 ≤ ⟪z, e₀⟫}` in
`EuclideanSpace ℝ (Fin (m + 2))` with `{z : EuclideanHalfSpace (m + 2) | ‖z.val‖ < 1}`. -/
private def halfBallUnitBallHomeomorph (m : ℕ) :
    let p : sphere (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 :=
      ⟨EuclideanSpace.single 0 1, mem_sphere_zero_iff_norm.mpr (by
        simpa only [EuclideanSpace.single, norm_one] using
          (PiLp.norm_single 2 (fun _ : Fin (m + 2) => ℝ) 0 1))⟩
    ↥(ball (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 ∩
        {z | 0 ≤ ⟪z, (p : EuclideanSpace ℝ (Fin (m + 2)))⟫}) ≃ₜ
      {z : EuclideanHalfSpace (m + 2) | ‖z.val‖ < 1} :=
  { toFun z := ⟨⟨z.val, by
      simpa [EuclideanSpace.inner_single_right] using z.property.2⟩,
      mem_ball_zero_iff.mp z.property.1⟩
    invFun z := ⟨z.val.val, mem_ball_zero_iff.mpr z.property, by
      simp [EuclideanSpace.inner_single_right]⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- Given a combinatorial `(m + 1)`-ball link at `v` and a homeomorphism `a` from the link
polyhedron to the closed `(m + 1)`-ball, build a half-space chart on `openStarRealization K v`
whose boundary hyperplane `c x 0 = 0` detects the sphere `‖a (starLinkProjection ...)‖ = 1`. -/
private theorem exists_openStar_halfSpace_chart_of_ball {K : AbstractSimplicialComplex ι}
    {m : ℕ} {v : ι}
    (hball : IsCombinatorialBall (link K.toPreAbstractSimplicialComplex {v}) (m + 1))
    (a : {y : Realization K | y.val.support ∈ K.link {v}} ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ∃ c : OpenPartialHomeomorph (Realization K) (EuclideanHalfSpace (m + 2)),
      c.source = openStarRealization K v ∧
      ∀ (x : Realization K) (hx : x ∈ K.openStarRealization v) (hlt : x.val v < 1),
        (c x).val 0 = 0 ↔
          ‖(a ⟨(starLinkProjection K v ⟨x, (K.mem_puncturedClosedStar v x).mpr
            ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩).val,
            (mem_geometricLink_iff K v _).mp (starLinkProjection K v _).property⟩ :
              EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := by
  let E := EuclideanSpace ℝ (Fin (m + 2))
  let p : sphere (0 : E) 1 := ⟨EuclideanSpace.single 0 1,
    mem_sphere_zero_iff_norm.mpr (by
      simpa only [E, EuclideanSpace.single, norm_one] using
        (PiLp.norm_single 2 (fun _ : Fin (m + 2) => ℝ) 0 1))⟩
  have hp : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
  let : Fact (Module.finrank ℝ E = m + 2) := ⟨by simp [E]⟩
  let b := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (m + 1) hp).repr.symm
  let d : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    b.toHomeomorph.subtype fun z => by simp
  let r := Homeomorph.setCongr (s := K.geometricLink v)
    (t := {y : Realization K | y.val.support ∈ K.link {v}})
    (Set.ext (mem_geometricLink_iff K v))
  let l := r.trans (a.trans (d.trans (TauCeti.hemisphereHomeomorph p).symm))
  have hcomp := K.isCompact_closedStarRealization
    (finite_faces_closedStar_iff.mpr hball.finite_faces)
  let f := openStarHomeomorphHalfBall hcomp l
  have hinner (z : E) : ⟪z, (p : E)⟫ = z 0 := by
    simp [p, E, EuclideanSpace.inner_single_right]
  have hU : IsOpen {z : EuclideanHalfSpace (m + 2) | ‖z.val‖ < 1} :=
    isOpen_lt continuous_subtypeVal.norm continuous_const
  obtain ⟨c, hc_src, -, hc_apply⟩ :=
    OpenPartialHomeomorph.exists_source_eq_target_eq_of_homeomorph
      (K.isOpen_openStarRealization v) hU (f.trans (halfBallUnitBallHomeomorph m))
      ⟨vertex K v, by simp [mem_openStarRealization]⟩
  refine ⟨c, hc_src, fun x hx hlt => ?_⟩
  let p₀ : puncturedClosedStar K v := ⟨x, (K.mem_puncturedClosedStar v x).mpr
    ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩
  let y : geometricLink K v := starLinkProjection K v p₀
  have hzero : (c x).val 0 = 0 ↔ ⟪((l y : sphere (0 : E) 1) : E), (p : E)⟫ = 0 := by
    have hcx : (c x).val = ((openStarHomeomorphHalfBall hcomp l ⟨x, hx⟩ : _) : E) :=
      congrArg (fun z : EuclideanHalfSpace (m + 2) => z.val) (hc_apply ⟨x, hx⟩)
    have h0eq : (c x).val 0 = ⟪(c x).val, (p : E)⟫ := (hinner _).symm
    rw [h0eq, hcx, coe_openStarHomeomorphHalfBall_apply,
      coe_closedStarHomeomorphHalfBall_of_lt hcomp l _ hlt, real_inner_smul_left,
      mul_eq_zero]
    have hne : 1 - x.val v ≠ 0 := (sub_pos.mpr hlt).ne'
    exact ⟨fun hor => hor.resolve_left hne, fun hir => Or.inr hir⟩
  have hhemi : ⟪((l y : sphere (0 : E) 1) : E), (p : E)⟫ = 0 ↔
      ‖(a (r y) : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 := by
    have h1 := TauCeti.norm_hemisphereHomeomorph_apply_eq_one_iff p (l y)
    have hl : TauCeti.hemisphereHomeomorph p (l y) = d (a (r y)) := by
      simp [l]
    rw [← h1, hl]
    simp [d, b]
  exact hzero.trans hhemi

/-- Pointwise boundary characterization for the realization of a combinatorial `(n + 1)`-manifold:
a point lies on the manifold boundary iff its support lies in `manifoldBoundary`. -/
theorem IsCombinatorialManifold.isBoundaryPoint_realizationChartedSpace_iff :
    ∀ {n : ℕ} {ι : Type u} [DecidableEq ι] {K : AbstractSimplicialComplex ι}
      (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1))
      (x : Realization K),
      letI := h.realizationChartedSpace
      (𝓡∂ (n + 1)).IsBoundaryPoint x ↔
        x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex
  | n, ι, _, K, h, x => by
    let := h.realizationChartedSpace
    obtain ⟨v, hx⟩ := K.exists_mem_openStarRealization x
    have hvsup : v ∈ x.val.support := (K.mem_openStarRealization_iff_mem_support).mp hx
    have hv : ({v} : Finset ι) ∈ K := singleton_mem_of_mem (support_mem K x) hvsup
    rcases (isCombinatorialManifold_succ_iff.mp h) hv with hsphere | hball
    · -- Interior vertex: `openStarRealization K v` embeds into the open half-space.
      obtain ⟨c, hc, -, -, -⟩ := hsphere.exists_openPartialHomeomorph_openStar_ball
      let j : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1)))
          (EuclideanHalfSpace (n + 1)) :=
        (TauCeti.EuclideanHalfSpace.isOpenEmbedding_interiorEmbedding n).toOpenPartialHomeomorph
      have hxs : x ∈ (c.trans j).source := by
        simpa [hc, j] using hx
      rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
        TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff]
      have hpos : 0 < ((c.trans j) x).val 0 := by
        simp [j, TauCeti.EuclideanHalfSpace.interiorEmbedding_coe_apply_zero, Real.exp_pos]
      refine iff_of_false hpos.ne' fun hxbd => ?_
      have hvbd : ({v} : Finset ι) ∈ manifoldBoundary K.toPreAbstractSimplicialComplex :=
        singleton_mem_of_mem hxbd hvsup
      exact hsphere.not_isCombinatorialBall (h.singleton_mem_manifoldBoundary_iff.mp hvbd)
    · -- Boundary vertex: split by `n = 0` vs `n = m + 1`.
      cases n with
      | zero =>
        obtain ⟨c, hc, -, -, hrad⟩ := hball.exists_openPartialHomeomorph_openStar_halfBall
        have hxs : x ∈ c.source := hc ▸ hx
        rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
          TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff]
        have hcoord : (c x).val 0 = 0 ↔ x.val v = 1 := by
          rw [← TauCeti.EuclideanHalfSpace.eq_zero_iff]
          have hnorm : ‖(c x).val‖ = 1 - x.val v := hrad ⟨x, hx⟩
          constructor
          · intro hcz
            rw [hcz] at hnorm
            have h0 : (0 : EuclideanHalfSpace 1).val = 0 := rfl
            rw [h0, norm_zero] at hnorm
            linarith
          · intro hx1
            apply Subtype.ext
            apply norm_eq_zero.mp
            linarith [hnorm]
        rw [hcoord]
        constructor
        · intro hx1
          have heq := (Realization.eq_vertex_iff K x v).mpr hx1
          have hsup : x.val.support = {v} := by
            rw [heq, vertex_val, Finsupp.support_single v one_ne_zero]
          rw [hsup]
          exact h.singleton_mem_manifoldBoundary_iff.mpr hball
        · intro hxbd
          obtain ⟨_, hb⟩ := h.mem_manifoldBoundary_iff.mp hxbd
          have hle : x.val.support.card ≤ 1 := h.card_le_of_link_ne_bot hb.ne_bot
          have hsup : x.val.support = {v} :=
            Finset.eq_singleton_iff_unique_mem.mpr
              ⟨hvsup, fun w hw => Finset.card_le_one.mp hle w hw v hvsup⟩
          have hxeq : x = vertex K v := Realization.eq_vertex_of_support_eq K x hsup
          simp [hxeq]
      | succ m =>
        by_cases hlt : x.val v < 1
        · -- Away from the vertex `v`, reduce radially to the `(m + 1)`-dimensional link.
          obtain ⟨a⟩ := hball.nonempty_homeomorph_closedBall (A := K) link_le
          obtain ⟨c, hc_src, hc_zero⟩ := exists_openStar_halfSpace_chart_of_ball hball a
          have hxs : x ∈ c.source := hc_src ▸ hx
          rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
            TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff, hc_zero x hx hlt]
          let Labs := (link K.toPreAbstractSimplicialComplex {v}).restrictToVertices
          have hLman : IsCombinatorialManifold Labs.toPreAbstractSimplicialComplex (m + 1) := by
            rw [← isCombinatorialManifold_map_iff (Subtype.val_injective (p := fun w : ι =>
              ({w} : Finset ι) ∈ link K.toPreAbstractSimplicialComplex {v})),
              map_val_restrictToVertices]
            exact hball.isCombinatorialManifold
          let := hLman.realizationChartedSpace
          let rLink := restrictToVerticesRealizationHomeomorph
            (K := K) (link_le (K := K.toPreAbstractSimplicialComplex) (σ := {v}))
          let eBall : Realization Labs ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 :=
            rLink.trans a
          let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
            ⟨by simp⟩
          let p₀ : puncturedClosedStar K v := ⟨x, (K.mem_puncturedClosedStar v x).mpr
            ⟨K.openStarRealization_subset_closedStarRealization v hx, hlt⟩⟩
          let y : {y : Realization K | y.val.support ∈ K.link {v}} :=
            ⟨(starLinkProjection K v p₀).val,
              (mem_geometricLink_iff K v _).mp (starLinkProjection K v p₀).property⟩
          have hbd_equiv : ‖(a y : EuclideanSpace ℝ (Fin (m + 1)))‖ = 1 ↔
              (𝓡∂ (m + 1)).IsBoundaryPoint (eBall (rLink.symm y)) := by
            rw [TauCeti.isBoundaryPoint_closedBall_iff (n := m + 1)]
            simp [eBall]
          rw [hbd_equiv, ← eBall.isBoundaryPoint_iff (𝓡∂ (m + 1)) (𝓡∂ (m + 1)) rfl _,
            hLman.isBoundaryPoint_realizationChartedSpace_iff (rLink.symm y),
            ← link_restrictToVerticesRealizationHomeomorph_support_mem_manifoldBoundary_iff v,
            Homeomorph.apply_symm_apply]
          exact (mem_manifoldBoundary_of_openStar_lt_one h hx hlt).symm
        · -- At the vertex `v` itself (`x = vertex K v`), both sides hold.
          have hx1 : x.val v = 1 := le_antisymm (Realization.le_one K x v) (not_lt.mp hlt)
          have heq : x = vertex K v := (Realization.eq_vertex_iff K x v).mpr hx1
          obtain ⟨c, hc, -, hcv, -⟩ := hball.exists_openPartialHomeomorph_openStar_halfBall
          have hxs : x ∈ c.source := hc ▸ hx
          rw [ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hxs,
            TauCeti.modelWithCornersEuclideanHalfSpace_mem_frontier_range_iff, heq, hcv]
          have hsup : (vertex K v).val.support = {v} := by simp
          rw [hsup]
          refine iff_of_true rfl (h.singleton_mem_manifoldBoundary_iff.mpr hball)

/-- The manifold boundary of the realization of a positive-dimensional combinatorial manifold
consists of the points whose carrier lies in `manifoldBoundary`. -/
theorem IsCombinatorialManifold.boundary_realizationChartedSpace {n : ℕ}
    {K : AbstractSimplicialComplex ι}
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    (𝓡∂ (n + 1)).boundary (Realization K) =
      {x : Realization K |
        x.val.support ∈ manifoldBoundary K.toPreAbstractSimplicialComplex} := by
  let := h.realizationChartedSpace
  ext x
  exact h.isBoundaryPoint_realizationChartedSpace_iff x

/-- The manifold interior of the realization of a positive-dimensional combinatorial manifold
consists of the points whose carrier avoids `manifoldBoundary`. -/
theorem IsCombinatorialManifold.interior_realizationChartedSpace {n : ℕ}
    {K : AbstractSimplicialComplex ι}
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex (n + 1)) :
    letI := h.realizationChartedSpace
    (𝓡∂ (n + 1)).interior (Realization K) =
      {x : Realization K |
        x.val.support ∉ manifoldBoundary K.toPreAbstractSimplicialComplex} := by
  let := h.realizationChartedSpace
  rw [← ModelWithCorners.compl_boundary, h.boundary_realizationChartedSpace]
  rfl

end PreAbstractSimplicialComplex
